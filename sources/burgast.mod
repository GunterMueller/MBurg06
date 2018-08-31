(*
 *  This program is copyright (c) 1995 Faculty of Information Technology,
 *  Queensland University of Technology, Brisbane, Australia.
 *  The program may be freely distributed in source or compiled form,
 *  provided this copyright notice remains intact in the sources. 
 *  Original program, June 1995, John Gough.
 *)
IMPLEMENTATION MODULE BurgAst;
  IMPORT 
	CardSequences, InOut, StdError, StdStrings, 
	BurgInOut, MburgS, Ascii, Types;
  FROM  BurgInOut IMPORT IdErrorMessage, trace;
  FROM  Storage   IMPORT ALLOCATE;

  VAR   index    : CARDINAL;
        thisProd : ProdIndex;
        ntTide   : CARDINAL;
     
  CONST maxLst     = 9;
  TYPE	HelperBlk  = POINTER TO StringList;
	StringList = 
	      RECORD
		strs : ARRAY [0 .. maxLst] OF ARRAY [0 .. 31] OF CHAR;
		next : [0 .. maxLst];
	      END;

  (* ============================================================= *)
  PROCEDURE SemanticError(n : CARDINAL);
  BEGIN
    MburgS.Error(n,1,1,1);
  END SemanticError;

  (* ============================================================= *)
  MODULE HashTable;
    FROM MburgS IMPORT CharAt;
    IMPORT CardSequences, MburgS, StdError;
    IMPORT 
	termInfo, TermRec, nonTermI, NTRecord, invalid, 
	unknown, ntTide, SemanticError, IdErrorMessage;

    EXPORT EnterNT, NewTerm, LookupT, maxT;

    CONST bNum   = 59;

   (*
    *   layout of 32 bits in cardinal is ---
    *
    *		[10987654321098765432109876543210]
    *		 <----pos(17)----><len6><idx(8)>\
    *						 \ isTerm (1)
    *)

    VAR table : ARRAY [0 .. bNum - 1] OF CardSequences.Sequence;
	ix    : CARDINAL;
	maxT  : CARDINAL;

    PROCEDURE Pack(isT : BOOLEAN; pos,len,idx : CARDINAL) : CARDINAL;
    BEGIN
      RETURN ORD(isT) + 2 * (idx + 256 * (len MOD 64 + 64 * pos));
    END Pack;

    PROCEDURE UnPack(crd : CARDINAL;
		     VAR isT : BOOLEAN;
		     VAR pos, len, idx : CARDINAL);
    BEGIN
      isT := ODD(crd);    crd := crd DIV 2;
      idx := crd MOD 256; crd := crd DIV 256;
      len := crd MOD 64;  pos := crd DIV 64;
    END UnPack;

    PROCEDURE Hash(pos,len : INTEGER) : CARDINAL;
      VAR idx   : INTEGER;
	  total : CARDINAL;
    BEGIN
      total := 0;
      FOR idx := 0 TO len - 1 DO
       (* $T- *)
	total := total * 2 + ORD(CharAt(pos + idx));
       (* $T= *)
      END;
      RETURN total MOD bNum;
    END Hash;

    PROCEDURE Equal(pos1,pos2,len : INTEGER) : BOOLEAN;
      VAR idx : INTEGER;
    BEGIN
      FOR idx := 0 TO len - 1 DO
	IF CharAt(pos1+idx) <> CharAt(pos2+idx) THEN RETURN FALSE END;
      END;
      RETURN TRUE;
    END Equal;

    PROCEDURE EnterNT(pos : INTEGER;
		      len : INTEGER;
		  VAR idx : INTEGER);
      VAR old : INTEGER;
    BEGIN
      LookupN(pos,len,old);
      IF old <> 0 THEN
	idx := old;
      ELSE
	INC(ntTide);
	idx := ntTide;
        CardSequences.InitSequence(nonTermI[idx].chainSeq);
        CardSequences.InitSequence(nonTermI[idx].prodIdxs);
	nonTermI[idx].pos := pos;
	nonTermI[idx].len := len;
        nonTermI[idx].reached := FALSE;
        nonTermI[idx].terminates := FALSE;
	CardSequences.LinkLeft(table[Hash(pos,len)],Pack(FALSE,pos,len,idx));
      END;
    END EnterNT;

    PROCEDURE NewTerm(pos : INTEGER;
		      len : INTEGER;
		      idx : INTEGER);
      VAR old : INTEGER;
    BEGIN
      LookupT(pos,len,old);
      IF old <> 0 THEN
	SemanticError(100);
        IdErrorMessage("terminal symbol",pos,len,"already defined");
      ELSIF termInfo[idx].termArity <> unknown THEN
	SemanticError(101);
        IdErrorMessage("terminal symbol",pos,len,"_and_");
        IdErrorMessage("terminal symbol",termInfo[idx].pos,
			termInfo[idx].len,"have same value");
      ELSIF idx <= 0 THEN
	SemanticError(102);
        IdErrorMessage("terminal symbol",pos,len,"must have a positive value");
      ELSE
	termInfo[idx].pos := pos;
	termInfo[idx].len := len;
	termInfo[idx].termArity := invalid;
	CardSequences.LinkLeft(table[Hash(pos,len)],Pack(TRUE,pos,len,idx));
	IF idx > INT(maxT) THEN maxT := idx END;
      END;
    END NewTerm;

    PROCEDURE LookupT(pos : INTEGER;
		      len : INTEGER;
		  VAR idx : INTEGER);
      VAR bkt : CARDINAL;
	  crs : CardSequences.ElemPtr;
	  elm : CARDINAL;
	  isTerm : BOOLEAN;
	  olP, olL, olI : CARDINAL;
    BEGIN
      bkt := Hash(pos,len);
      CardSequences.InitCursor(table[bkt],crs);
      WHILE NOT CardSequences.Ended(crs) DO
	CardSequences.GetNext(crs,elm);
	UnPack(elm,isTerm,olP,olL,olI);
	IF isTerm AND (olL = ORD(len)) AND Equal(pos,olP,len) THEN
	  idx := olI; RETURN;			(* PREMATURE RETURN *)
	END;
      END;
      idx := 0;
    END LookupT;

    PROCEDURE LookupN(pos : INTEGER;
		      len : INTEGER;
		  VAR idx : INTEGER);
      VAR bkt : CARDINAL;
	  crs : CardSequences.ElemPtr;
	  elm : CARDINAL;
	  isTerm : BOOLEAN;
	  olP, olL, olI : CARDINAL;
    BEGIN
      bkt := Hash(pos,len);
      CardSequences.InitCursor(table[bkt],crs);
      WHILE NOT CardSequences.Ended(crs) DO
	CardSequences.GetNext(crs,elm);
	UnPack(elm,isTerm,olP,olL,olI);
	IF NOT isTerm AND (olL = ORD(len)) AND Equal(pos,olP,len) THEN
	  idx := olI; RETURN;			(* PREMATURE RETURN *)
	END;
      END;
      idx := 0;
    END LookupN;

  BEGIN
    maxT := 0;
    FOR ix := 0 TO bNum - 1 DO
      CardSequences.InitSequence(table[ix]);
    END;
  END HashTable;

 (* ==================== Ast Building Procedures ===================== *)

  PROCEDURE Terminates(this : Tree) : BOOLEAN;
  BEGIN
    WITH this^ DO
      IF isChain AND nonTermI[nonTerm].terminates THEN RETURN TRUE;
      ELSIF NOT isChain THEN (* a terminal symbol *)
	CASE termInfo[terminal].termArity OF
        | 0 : RETURN TRUE;
	| 1 : RETURN Terminates(left);
	| 2 : RETURN Terminates(left) AND Terminates(right);
        END;
      ELSE RETURN FALSE;
      END;
    END;
  END Terminates;

  PROCEDURE EnterProd  (tPos : INTEGER;
			lhsN : NonTermIx;
			tree : Tree;
                    VAR prod : ProdIndex);
  BEGIN
    INC(thisProd);
    WITH prodInfo[thisProd] DO
      prodCost   := 0;
      textBegin  := tPos;
      textLength := MburgS.pos + INT(MburgS.len) - tPos;
      lhsNonTerm := lhsN;
      rhs        := tree;
      semEnd     := 0;
      semPos     := 0;
      semCol     := 1;
      decEnd     := 0;
      decPos     := 0;
      decCol     := 1;
      GetHelperList(thisProd,strings);
    END;
    CardSequences.LinkRight(nonTermI[lhsN].prodIdxs,thisProd);
    IF Terminates(tree) THEN nonTermI[lhsN].terminates := TRUE END;
    prod := thisProd;
  END EnterProd;

  PROCEDURE EnterArity(idx : TermIndex; arity : INTEGER);
  BEGIN
    WITH termInfo[idx] DO
      IF termArity = invalid THEN
	termArity := arity;
      ELSIF termArity <> arity THEN
	SemanticError(103);
        IdErrorMessage("terminal symbol",pos,len,"has contradictory arity");
      END;
    END;
  END EnterArity;

  PROCEDURE NewTmTree(idx : TermIndex) : Tree;
    VAR tree : Tree;
  BEGIN
    NEW(tree); 
    tree^.left  := NIL;
    tree^.right := NIL;
    tree^.isChain  := FALSE;
    tree^.terminal := idx;
    RETURN tree;
  END NewTmTree;

  PROCEDURE NewNtTree(idx : NonTermIx) : Tree;
    VAR tree : Tree;
  BEGIN
    NEW(tree); 
    tree^.left  := NIL;
    tree^.right := NIL;
    tree^.isChain := TRUE;
    tree^.nonTerm := idx;
    RETURN tree;
  END NewNtTree;

 (* =================== Semantic Check Procedures ==================== *)

  PROCEDURE Check;

    PROCEDURE MarkTree(this : Tree);
    BEGIN
      IF this^.isChain THEN
	MarkReached(this^.nonTerm);
      ELSE
        IF this^.left <> NIL THEN 
	  MarkTree(this^.left);
          IF this^.right <> NIL THEN 
	    MarkTree(this^.right);
	  END;
	END;
      END;
    END MarkTree;

    PROCEDURE MarkReached(ntSy : NonTermIx);
      VAR curs : CardSequences.ElemPtr;
	  prNm : CARDINAL;
    BEGIN
      IF nonTermI[ntSy].reached THEN RETURN END;
      nonTermI[ntSy].reached := TRUE;
      CardSequences.InitCursor(nonTermI[ntSy].prodIdxs,curs);
      IF CardSequences.Ended(curs) THEN
	SemanticError(104);
        IdErrorMessage("non terminal symbol",nonTermI[ntSy].pos,
		        nonTermI[ntSy].len,"has no productions");
      END;
      WHILE NOT CardSequences.Ended(curs) DO
	CardSequences.GetNext(curs,prNm);
	MarkTree(prodInfo[prNm].rhs);
      END;
    END MarkReached;

    PROCEDURE CheckTerminates(ntSy : NonTermIx;
			  VAR got1 : BOOLEAN);
      VAR curs : CardSequences.ElemPtr;
	  prNm : CARDINAL;
    BEGIN
     (* skip if already known to terminate *)
      IF nonTermI[ntSy].terminates THEN RETURN END;
     (* otherwise check all productions for ntSy *)
      CardSequences.InitCursor(nonTermI[ntSy].prodIdxs,curs);
      WHILE NOT CardSequences.Ended(curs) DO
	CardSequences.GetNext(curs,prNm);
	IF Terminates(prodInfo[prNm].rhs) THEN
	  got1 := TRUE;
	  nonTermI[ntSy].terminates := TRUE;
	 (* one hit is enough! *) RETURN;
        END;
      END;
    END CheckTerminates;

    VAR index : NonTermIx;
	chng  : BOOLEAN;

  BEGIN
    IF BurgInOut.verbose THEN 
      InOut.WriteString("# Mburg: checking grammar");
      InOut.WriteLn;
    END;
   (*
    *  First, check that every non-term is reachable.
    *)
    MarkReached(goalSmbl);
   (* 
    *  Next, check that every non-term is terminating.
    *
    *  The algorithm is naive, and is much slower than
    *  the usual worklist algorithm.  But the worklist
    *  algorithm requires the creation of a dependency
    *  graph before it is applied. So this is better.
    *)
    REPEAT
      chng := FALSE;
      FOR index := 1 TO ntTide DO CheckTerminates(index,chng) END;
    UNTIL NOT chng;
   (* 
    *  now check the outcomes in the Boolean flags.
    *)
    FOR index := 1 TO ntTide DO
      IF NOT nonTermI[index].reached THEN
	SemanticError(105);
        IdErrorMessage("non terminal symbol",nonTermI[index].pos,
		        nonTermI[index].len,"cannot be reached");
      ELSIF NOT nonTermI[index].terminates THEN
	SemanticError(106);
        IdErrorMessage("non terminal symbol",nonTermI[index].pos,
		        nonTermI[index].len,"does not terminate");
      END;
    END;
  END Check;

 (* ================================================================== *)
 (* ===================    Semantic Processing    ==================== *)
 (* ================================================================== *)

  PROCEDURE WriteSymbol(pos,len : INTEGER);
    VAR str : ARRAY [0 .. 127] OF CHAR;
  BEGIN
    MburgS.GetString(pos,len,str);
    BurgInOut.WriteSmm(str);
  END WriteSymbol;

  PROCEDURE WriteNT(nt : NonTermIx);
  BEGIN
    WriteSymbol(nonTermI[nt].pos,nonTermI[nt].len);
  END WriteNT;

  PROCEDURE WriteT(ts : TermIndex);
  BEGIN
    WriteSymbol(termInfo[ts].pos,termInfo[ts].len);
  END WriteT;

  PROCEDURE WritePI(crd : CARDINAL);
  BEGIN
    IF crd > 9 THEN WritePI(crd DIV 10) END;
    BurgInOut.WriteCmm(CHR(crd MOD 10 + ORD('0')));
  END WritePI;

  PROCEDURE Indent(in : CARDINAL);
  BEGIN
    WHILE in > 0 DO BurgInOut.WriteCmm(" "); DEC(in) END;
  END Indent;

  PROCEDURE EmitProdComment(pi : ProdIndex; in : CARDINAL);
  BEGIN
    Indent(in);
    BurgInOut.WriteSmm(" (* Prod "); 
    WritePI(pi); 
    BurgInOut.WriteSmm(" <"); 
    WriteSymbol(prodInfo[pi].textBegin,prodInfo[pi].textLength);
    BurgInOut.WriteSmm("> *)"); 
    BurgInOut.WriteLmm();
  END EmitProdComment;

  PROCEDURE EmitTrace(pi : ProdIndex; in : CARDINAL);
    VAR str : ARRAY [0 .. 127] OF CHAR;
  BEGIN
    Indent(in);
    BurgInOut.WriteSmm("  InOut.WriteCard("); 
    WriteCost(pi); 
    BurgInOut.WriteSmm(",3);");
    BurgInOut.WriteLmm;
    Indent(in);
    BurgInOut.WriteSmm(
	"  FOR count := 0 TO traceDepth * 2 DO InOut.Write(' ') END;"); 
    BurgInOut.WriteLmm;
    Indent(in);
(*
 *  BurgInOut.WriteSmm("  InOut.WriteString('Prod "); 
 *  WritePI(pi); 
 *  BurgInOut.WriteSmm(" <"); 
 *)
    BurgInOut.WriteSmm("  InOut.WriteString('<"); 
    WriteSymbol(prodInfo[pi].textBegin,prodInfo[pi].textLength);
    BurgInOut.WriteCmm(">");
    IF prodInfo[pi].predBegin <> 0 THEN 
      BurgInOut.WriteSmm(" & ");
      WITH prodInfo[pi] DO
        MburgS.GetString(predBegin,predLength,str);
        ExpandString(str,strings);
      END;
    END;
    BurgInOut.WriteSmm(" ');"); BurgInOut.WriteLmm;
    Indent(in);
    BurgInOut.WriteSmm("  InOut.WriteLn;"); 
    BurgInOut.WriteLmm;
  END EmitTrace;

 (* ================================================================== *)
 (* ===================  Emit Matcher Procedures  ==================== *)
 (* ================================================================== *)

  PROCEDURE MakeInitializers;
    CONST max      = MAX(Types.Card16);
    TYPE  StateVec = ARRAY NonTermIx OF INTEGER;
    VAR   costs : StateVec;
	  rules : StateVec;
	  index : TermIndex;
	  prodI : CARDINAL;
	  ntIdx : CARDINAL;
	  count : CARDINAL;
	  curs  : CardSequences.ElemPtr;

    PROCEDURE CCinsert(prod : ProdIndex; 
		       cost : INTEGER; 
		       VAR costZ,ruleZ : StateVec);
      VAR prodI : CARDINAL;
	  curs  : CardSequences.ElemPtr;
    BEGIN
      WITH prodInfo[prod] DO
	IF cost < costZ[lhsNonTerm] THEN
	  costZ[lhsNonTerm] := cost;
	  ruleZ[lhsNonTerm] := prod;
	  CardSequences.InitCursor(nonTermI[lhsNonTerm].chainSeq,curs);
	  WHILE NOT CardSequences.Ended(curs) DO
	    CardSequences.GetNext(curs,prodI);
	    CCinsert(prodI,
		cost + prodInfo[prodI].prodCost,
		costZ,ruleZ);
	  END; 
	END;
      END;
    END CCinsert;

  BEGIN
   (*
    *  Create an initializer for every leaf terminal
    *)
    BurgInOut.WriteSmm("  CONST allMaxCost = CostType{max BY "); 
    WritePI(ntTide + 1); BurgInOut.WriteSmm("};"); BurgInOut.WriteLmm;
    BurgInOut.WriteSmm("        allMaxProd = ProdType{0 BY "); 
    WritePI(ntTide + 1); BurgInOut.WriteSmm("};"); 
    BurgInOut.WriteLmm; BurgInOut.WriteLmm;

    FOR index := 0 TO maxT DO
      IF termInfo[index].termArity = 0 THEN
        FOR ntIdx := 0 TO ntTide DO
	  costs[ntIdx] := max;
	  rules[ntIdx] := 0;
	END;
	CardSequences.InitCursor(termInfo[index].prodList,curs);
	WHILE NOT CardSequences.Ended(curs) DO
         (*
	  *  The rhs of production prodI is
	  *  just the terminal symbol index.
	  *  Insert the cost at compile-compile time.
	  *)
	  CardSequences.GetNext(curs,prodI);
	  CCinsert(prodI,prodInfo[prodI].prodCost,costs,rules);
	END;
	BurgInOut.WriteSmm("  CONST "); WriteT(index);
	BurgInOut.WriteSmm("InitCost = CostType"); BurgInOut.WriteLmm;
	BurgInOut.WriteSmm("	(* cost *) {"); 
        ntIdx := 0;
	WHILE ntIdx <= ntTide DO
	  count := 0;
	  WHILE (ntIdx <= ntTide) AND
		(costs[ntIdx] = max) DO INC(count); INC(ntIdx) END;
	  IF count = 0 THEN
	    WritePI(costs[ntIdx]); INC(ntIdx);
	  ELSIF count = 1 THEN
	    BurgInOut.WriteSmm("max");
	  ELSE
	    BurgInOut.WriteSmm("max BY "); WritePI(count);
	  END;
	  IF ntIdx <= ntTide THEN BurgInOut.WriteCmm(",") END;
	END;
	BurgInOut.WriteSmm("};"); BurgInOut.WriteLmm;
	BurgInOut.WriteSmm("        "); WriteT(index);
	BurgInOut.WriteSmm("InitProd = ProdType"); BurgInOut.WriteLmm;
	BurgInOut.WriteSmm("	(* rule *) {"); 
        ntIdx := 0;
	WHILE ntIdx <= ntTide DO
	  count := 0;
	  WHILE (ntIdx <= ntTide) AND
		(rules[ntIdx] = 0) DO INC(count); INC(ntIdx) END;
	  IF count = 0 THEN
	    WritePI(rules[ntIdx]); INC(ntIdx);
	  ELSIF count = 1 THEN
	    BurgInOut.WriteCmm("0");
	  ELSE
	    BurgInOut.WriteSmm("0 BY "); WritePI(count);
	  END;
	  IF ntIdx <= ntTide THEN BurgInOut.WriteCmm(",") END;
	END;
	BurgInOut.WriteSmm("};"); BurgInOut.WriteLmm;
	BurgInOut.WriteLmm;
      END;
    END;
  END MakeInitializers;

  PROCEDURE WriteCost(prod  : ProdIndex);
  BEGIN
    CASE prodInfo[prod].nonZeros OF
    | 0 : BurgInOut.WriteCmm("0"); 
    | 1 : WritePI(prodInfo[prod].prodCost); 
    | 2 : BurgInOut.WriteSmm("rCost"); 
    | 3 : BurgInOut.WriteSmm("rCost + "); 
	  WritePI(prodInfo[prod].prodCost); 
    | 4 : BurgInOut.WriteSmm("lCost"); 
    | 5 : BurgInOut.WriteSmm("lCost + "); 
	  WritePI(prodInfo[prod].prodCost); 
    | 6 : BurgInOut.WriteSmm("lCost + rCost"); 
    | 7 : BurgInOut.WriteSmm("lCost + rCost + "); 
	  WritePI(prodInfo[prod].prodCost); 
    END;
  END WriteCost;

  PROCEDURE GenerateMatchers;
    CONST NL    = BurgInOut.WriteLmm;

    PROCEDURE WritePred(prod : ProdIndex; id : CARDINAL);
      VAR str : ARRAY [0 .. 127] OF CHAR;
    BEGIN
      IF id > 0 THEN 
	BurgInOut.WriteSmm(" AND"); NL;
        DEC(id); (* take one off for the explicit "(" *)
      END; 
      Indent(id);
      WITH prodInfo[prod] DO
	MburgS.GetString(predBegin,predLength,str);
	ExpandString(str,strings);
      END;
    END WritePred;

    PROCEDURE WriteInsert(prod  : ProdIndex;
			  arity : CARDINAL;
			  depth : CARDINAL);
    BEGIN
      Indent(depth);
      BurgInOut.WriteSmm("Insert");
      WriteNT(prodInfo[prod].lhsNonTerm); 
      BurgInOut.WriteSmm("(self,"); 
      WritePI(prod); 
      BurgInOut.WriteCmm(","); 
      WriteCost(prod);
      BurgInOut.WriteSmm(");"); NL;
    END WriteInsert;

    PROCEDURE EmitTreeMatch(tree   : Tree;
			    prefix : ARRAY OF CHAR;
			    id, dp : CARDINAL);
      VAR str : ARRAY [0 .. 127] OF CHAR;
    BEGIN
      IF dp <> 0 THEN 
	BurgInOut.WriteSmm(" AND"); NL; Indent(id); 
      END;
      IF tree^.isChain THEN
        BurgInOut.WriteCmm("("); 
        BurgInOut.WriteSmm(prefix); 
        BurgInOut.WriteSmm("^.$S.rules[");
        WriteNT(tree^.nonTerm); 
        BurgInOut.WriteSmm("] <> 0)");
      ELSE
        BurgInOut.WriteCmm("("); 
        BurgInOut.WriteSmm(prefix); 
        BurgInOut.WriteSmm("^.$O = "); 
        WriteT(tree^.terminal); 
        BurgInOut.WriteCmm(")"); 
	IF tree^.left <> NIL THEN
	  StdStrings.Assign(prefix,str);
	  StdStrings.Append("^.$L",str);
	  EmitTreeMatch(tree^.left,str,id,dp+1);
	  IF tree^.right <> NIL THEN
	    StdStrings.Assign(prefix,str);
	    StdStrings.Append("^.$R",str);
	    EmitTreeMatch(tree^.right,str,id,dp+1);
	  END;
	END;
      END;
    END EmitTreeMatch;

    PROCEDURE EmitCostSum(tree   : Tree;
			  prefix : ARRAY OF CHAR;
			  depth  : CARDINAL);
      VAR str : ARRAY [0 .. 127] OF CHAR;
    BEGIN
      IF depth <> 0 THEN 
	BurgInOut.WriteSmm(" +"); NL;
	BurgInOut.WriteSmm(Ascii.ht); 
	BurgInOut.WriteSmm(Ascii.ht);
      END;
      IF tree^.isChain THEN
        BurgInOut.WriteSmm(prefix); 
        BurgInOut.WriteSmm("^.$S.costs[");
        WriteNT(tree^.nonTerm); 
        BurgInOut.WriteCmm("]");
      ELSE
	IF tree^.left <> NIL THEN
	  StdStrings.Assign(prefix,str);
	  StdStrings.Append("^.$L",str);
	  EmitCostSum(tree^.left,str,depth);
	  IF tree^.right <> NIL THEN
	    StdStrings.Assign(prefix,str);
	    StdStrings.Append("^.$R",str);
	    EmitCostSum(tree^.right,str,depth+1);
	  END;
	ELSE (* is a terminal leaf node ... *)
	  BurgInOut.WriteCmm("0");
	END;
      END;
    END EmitCostSum;

    PROCEDURE DoArityOne(prods : CardSequences.Sequence);
      VAR curs  : CardSequences.ElemPtr;
	  prod  : CARDINAL;
	  usedL : ARRAY NonTermIx OF CardSequences.Sequence;
	  index : NonTermIx;
    BEGIN
      BurgInOut.WriteSmm("   (* recurse to child *)"); NL;
      BurgInOut.WriteSmm("    match[self^.$L^.$O](self^.$L);"); NL;
      BurgInOut.WriteSmm("   (* now match patterns *)"); NL;
      FOR index := 0 TO ntTide DO
        CardSequences.InitSequence(usedL[index]);
      END;
     (*
      *  prods is the production list for this terminal.
      *  usedL is a list for this terminal with a given
      *  non-terminal symbol as its left sub-tree
      *)
      CardSequences.InitCursor(prods,curs);
      WHILE NOT CardSequences.Ended(curs) DO
	CardSequences.GetNext(curs,prod);
	IF prodInfo[prod].rhs^.left^.isChain THEN
	  index := prodInfo[prod].rhs^.left^.nonTerm;
	  CardSequences.LinkRight(usedL[index],prod);
	ELSE (* nested pattern *)
	  CardSequences.LinkRight(usedL[0],prod);
	END;
      END;
     (*
      *  now emit the various patterns for each nonterm
      *)
      FOR index := 1 TO ntTide DO
	IF NOT CardSequences.IsEmpty(usedL[index]) THEN
	  CardSequences.GetFirst(usedL[index],curs,prod);

	  BurgInOut.WriteSmm("    IF (self^.$L^.$S.rules["); 
	  WriteNT(index); 
	  BurgInOut.WriteSmm("] <> 0)"); 
	 (*
	  *  beware that not all have, or do not have, preds!
	  *)
	  IF CardSequences.Ended(curs) THEN
	   (*
	    *  One matching production in this group
	    * 
	    *   IF <match> THEN
	    *     <get left cost>
	    *     Insert()		_OR_
	    *
	    *   IF <match> AND
	    *      <pred> THEN
	    *     <get left cost>
	    *     Insert()
	    *)
	    IF prodInfo[prod].predBegin <> 0 THEN WritePred(prod,8) END;
	    BurgInOut.WriteSmm(" THEN"); NL;
	    EmitProdComment(prod,4);
	    BurgInOut.WriteSmm("      lCost := self^.$L^.$S.costs[");
	    WriteNT(index); 
	    BurgInOut.WriteSmm("];"); NL;
	    IF trace THEN EmitTrace(prod,6) END;
	    WriteInsert(prod,1,6);
	  ELSE
	   (*
	    *  Multiple matching prods in this group
	    * 
	    *   IF <match> THEN
	    *     <get left cost>
	    *     Insert()
	    *     Insert() ...		_OR_
	    *
	    *   IF <match> THEN
	    *     <get left cost>
	    *    IF <pred> THEN Insert() END;
	    *    IF <pred> THEN Insert() END; ...
	    *)
	    BurgInOut.WriteSmm(" THEN"); NL;
	    BurgInOut.WriteSmm("      lCost := self^.$L^.$S.costs[");
	    WriteNT(index); 
	    BurgInOut.WriteSmm("];"); NL;
	    IF prodInfo[prod].predBegin <> 0 THEN 
	      BurgInOut.WriteSmm("      IF "); WritePred(prod,0);
	      BurgInOut.WriteSmm(" THEN"); NL;
	      IF trace THEN EmitTrace(prod,8) END;
	      WriteInsert(prod,1,8);
	      BurgInOut.WriteSmm("      END;"); NL;
	    ELSE
	      IF trace THEN EmitTrace(prod,6) END;
	      WriteInsert(prod,1,6); NL;
	    END;
	    WHILE NOT CardSequences.Ended(curs) DO
	      CardSequences.GetNext(curs,prod);
	      IF prodInfo[prod].predBegin <> 0 THEN 
	        BurgInOut.WriteSmm("      IF "); WritePred(prod,0);
	        BurgInOut.WriteSmm(" THEN"); NL;
	        IF trace THEN EmitTrace(prod,8) END;
	        WriteInsert(prod,1,8);
	        BurgInOut.WriteSmm("      END;"); NL;
	      ELSE
	        IF trace THEN EmitTrace(prod,6) END;
	        WriteInsert(prod,1,6); NL;
	      END; (* if *)
	    END; (* while *)
	  END;
	  BurgInOut.WriteSmm("    END;"); NL;
        END;
      END;
      IF NOT CardSequences.IsEmpty(usedL[0]) THEN
       (*
	*  For each production in this group
	* 
	*   IF <tree-match> THEN
	*     <get left cost>
	*     Insert() 			_OR_
	*
	*   IF <tree-match> AND
	*      <pred> THEN
	*     <get left cost>
	*     Insert()
	*)
	CardSequences.InitCursor(usedL[0],curs);
	WHILE NOT CardSequences.Ended(curs) DO

	  CardSequences.GetNext(curs,prod);

	  BurgInOut.WriteSmm("    IF ");
	  EmitTreeMatch(prodInfo[prod].rhs^.left,"self^.$L",7,0);
	  IF prodInfo[prod].predBegin <> 0 THEN WritePred(prod,8) END;
	  BurgInOut.WriteSmm(" THEN"); NL;
	  EmitProdComment(prod,4);
	  IF prodInfo[prod].nonZeros >= 4 THEN
	    BurgInOut.WriteSmm("      lCost := ");
	    EmitCostSum(prodInfo[prod].rhs^.left,"self^.$L",0);
	    BurgInOut.WriteCmm(";"); NL;
	  END;

	  IF trace THEN EmitTrace(prod,6) END;
	  WriteInsert(prod,1,6);
	  BurgInOut.WriteSmm("    END;"); NL;

	END;
      END;
    END DoArityOne;

    PROCEDURE DoArityTwo(prods : CardSequences.Sequence);
      VAR curs  : CardSequences.ElemPtr;
	  prod  : CARDINAL;
	  usedL : ARRAY NonTermIx OF CardSequences.Sequence;
	  index : NonTermIx;
    BEGIN
      BurgInOut.WriteSmm("   (* recurse to children *)"); NL;
      BurgInOut.WriteSmm("    match[self^.$L^.$O](self^.$L);"); NL;
      BurgInOut.WriteSmm("    match[self^.$R^.$O](self^.$R);"); NL;
      BurgInOut.WriteSmm("   (* now match patterns *)"); NL;
      FOR index := 0 TO ntTide DO
        CardSequences.InitSequence(usedL[index]);
      END;
     (*
      *  prods is the production list for this terminal.
      *  usedL is a list for this terminal with a given
      *  non-terminal symbol as its left sub-tree
      *)
      CardSequences.InitCursor(prods,curs);
      WHILE NOT CardSequences.Ended(curs) DO
	CardSequences.GetNext(curs,prod);
	IF prodInfo[prod].rhs^.left^.isChain THEN
	  index := prodInfo[prod].rhs^.left^.nonTerm;
	  CardSequences.LinkRight(usedL[index],prod);
	ELSE (* nested pattern *)
	  CardSequences.LinkRight(usedL[0],prod);
	END;
      END;
     (*
      *  now emit the various patterns for each nonterm
      *)
      FOR index := 1 TO ntTide DO
       (*
	*  For each production group
	* 
	*   IF <match> THEN			Once only
	*     <get left cost>
        *     --------------------------+
	*     IF <tree-match> THEN	|	Repeated for each
	*       <get right cost>	|	element of list
	*       Insert()		|
	*     END		_OR_	|
	*     IF <tree-match> AND	|
	*        <pred> THEN		|
	*       <get right cost>	|
	*       Insert()		|
	*     END			|
        *     --------------------------+
	*   END;				Once only
	*)
	IF NOT CardSequences.IsEmpty(usedL[index]) THEN
	  BurgInOut.WriteSmm("    IF self^.$L^.$S.rules["); 
	  WriteNT(index); 
	  BurgInOut.WriteSmm("] <> 0 THEN"); NL;

	  BurgInOut.WriteSmm("      lCost := self^.$L^.$S.costs[");
	  WriteNT(index); 
	  BurgInOut.WriteSmm("];"); NL;

	  CardSequences.InitCursor(usedL[index],curs);
	  WHILE NOT CardSequences.Ended(curs) DO

	    CardSequences.GetNext(curs,prod);

	    BurgInOut.WriteSmm("      IF ");
	    EmitTreeMatch(prodInfo[prod].rhs^.right,"self^.$R",9,0);
	    IF prodInfo[prod].predBegin <> 0 THEN WritePred(prod,10) END;
	    BurgInOut.WriteSmm(" THEN"); NL;
	    EmitProdComment(prod,6);
	    IF prodInfo[prod].nonZeros MOD 4 >= 2 THEN
	      BurgInOut.WriteSmm("        rCost := ");
	      EmitCostSum(prodInfo[prod].rhs^.right,"self^.$R",0);
	      BurgInOut.WriteCmm(";"); NL;
	    END;

	    IF trace THEN EmitTrace(prod,8) END;
	    WriteInsert(prod,2,8);
	    BurgInOut.WriteSmm("      END;"); NL;

	  END;
	  BurgInOut.WriteSmm("    END;"); NL;
	END;
      END;
      IF NOT CardSequences.IsEmpty(usedL[0]) THEN
	CardSequences.InitCursor(usedL[0],curs);
	WHILE NOT CardSequences.Ended(curs) DO

	  CardSequences.GetNext(curs,prod);

	  BurgInOut.WriteSmm("    IF ");
	  EmitTreeMatch(prodInfo[prod].rhs^.left,"self^.$L",7,0);
	  EmitTreeMatch(prodInfo[prod].rhs^.right,"self^.$R",7,1);
	  IF prodInfo[prod].predBegin <> 0 THEN WritePred(prod,8) END;
	  BurgInOut.WriteSmm(" THEN"); NL;
	  EmitProdComment(prod,4);
	  IF prodInfo[prod].nonZeros >= 4 THEN
	    BurgInOut.WriteSmm("      lCost := ");
	    EmitCostSum(prodInfo[prod].rhs^.left,"self^.$L",0);
	    BurgInOut.WriteCmm(";"); NL;
	  END;

	  IF prodInfo[prod].nonZeros MOD 4 >= 2 THEN
	    BurgInOut.WriteSmm("      rCost := ");
	    EmitCostSum(prodInfo[prod].rhs^.right,"self^.$R",0);
	    BurgInOut.WriteCmm(";"); NL;
	  END;

	  IF trace THEN EmitTrace(prod,6) END;
	  WriteInsert(prod,2,6);
	  BurgInOut.WriteSmm("    END;"); NL;

	END;
      END;
    END DoArityTwo;

    PROCEDURE IsLeaf(t : Tree) : BOOLEAN;
    BEGIN
      RETURN NOT t^.isChain AND (t^.left = NIL);
    END IsLeaf;

    VAR index : TermIndex;
	arity : INTEGER;

  BEGIN  (* GenerateMatchers *)
    BurgInOut.WriteSmm(
    " (* ============== Pattern matching procedures ============= *)"); NL;NL;
    FOR index := 1 TO thisProd DO
      WITH prodInfo[index] DO
	IF prodCost > 0 THEN nonZeros := 1 END;
	IF (rhs^.right <> NIL) AND NOT IsLeaf(rhs^.right) THEN
	  INC(nonZeros,2);
	END;
	IF (rhs^.left <> NIL) AND NOT IsLeaf(rhs^.left) THEN
	  INC(nonZeros,4);
	END;
      END;
    END;
    FOR index := 1 TO maxT DO
      arity := termInfo[index].termArity;
      WITH termInfo[index] DO
        BurgInOut.ModProcM(pos,len);
	IF trace THEN BurgInOut.WriteSmm("    INC(traceDepth);"); NL END;
        IF arity = 0 THEN
	 (* do allocate here if necessary *)
	  BurgInOut.WriteSmm("    $Nself^.$S.costs := "); WriteT(index);
	  BurgInOut.WriteSmm("InitCost;"); NL;
	  BurgInOut.WriteSmm("    self^.$S.rules := "); WriteT(index);
	  BurgInOut.WriteSmm("InitProd;"); NL;
	  WriteStaticActions(index);
        ELSE 
	 (* do allocate here if necessary *)
	  BurgInOut.WriteSmm("    $Nself^.$S.costs := allMaxCost;"); NL;
	  BurgInOut.WriteSmm("    self^.$S.rules := allMaxProd;"); NL;
	  IF arity = 1 THEN
	    DoArityOne(prodList);
	  ELSE
	    DoArityTwo(prodList);
	  END;
	END;
	IF trace THEN BurgInOut.WriteSmm("    DEC(traceDepth);"); NL END;
        BurgInOut.EndProcM(pos,len);
      END; (* with *)
    END;
  END GenerateMatchers;

 (* ================================================================== *)
 (* ===================  Emit Insert Procedures  ===================== *)
 (* ================================================================== *)

  PROCEDURE GenerateInserts;
    VAR index : NonTermIx;
	chain : CARDINAL;
	curs  : CardSequences.ElemPtr;
  BEGIN
    BurgInOut.WriteSmm(
    " (* ==============  Cost insertion procedures  ============= *)");
    BurgInOut.WriteLmm; BurgInOut.WriteLmm;
    FOR index := 1 TO ntTide DO
      BurgInOut.ModProcI(nonTermI[index].pos,nonTermI[index].len);
      BurgInOut.WriteSmm("    IF self^.$S.costs["); WriteNT(index); 
      BurgInOut.WriteSmm("] > cost THEN"); BurgInOut.WriteLmm;
      BurgInOut.WriteSmm("      self^.$S.costs["); WriteNT(index); 
      BurgInOut.WriteSmm("] := cost;"); BurgInOut.WriteLmm;
      BurgInOut.WriteSmm("      self^.$S.rules["); WriteNT(index); 
      BurgInOut.WriteSmm("] := rule;"); BurgInOut.WriteLmm;
      BurgInOut.WriteSmm("     (* now any chain rules for this NT *)"); 
      BurgInOut.WriteLmm;
      CardSequences.InitCursor(nonTermI[index].chainSeq,curs);
      WHILE NOT CardSequences.Ended(curs) DO
        CardSequences.GetNext(curs,chain);
        WITH prodInfo[chain] DO
          BurgInOut.WriteSmm("      Insert"); WriteNT(lhsNonTerm); 
	  BurgInOut.WriteSmm("(self,"); WritePI(chain);
	  BurgInOut.WriteSmm(",cost");
	  IF prodCost > 0 THEN
	    BurgInOut.WriteCmm("+"); WritePI(prodCost); 
	  END;
	  BurgInOut.WriteSmm(");"); BurgInOut.WriteLmm;
	END;
      END;
      BurgInOut.WriteSmm("    END;"); BurgInOut.WriteLmm;
      BurgInOut.EndProcI(nonTermI[index].pos,nonTermI[index].len);
    END;
  END GenerateInserts;

 (* ================================================================== *)
 (* ====================   Emit Reduce Helpers   ===================== *)
 (* ================================================================== *)

  PROCEDURE ExpandString(str : ARRAY OF CHAR;
		 	 lst : HelperBlk);
    VAR ch : CHAR;
	ix : CARDINAL;
	ds : ARRAY [0 ..2] OF CHAR;
  BEGIN
    ch := str[0]; ix := 1;
    WHILE ch <> "" DO
      IF ch = "%" THEN
	ch := str[ix]; INC(ix);
	IF (ch >= "0") AND (ch <= "9") THEN
	  BurgInOut.WriteSmm("self");
	  BurgInOut.WriteSmm(lst^.strs[ORD(ch) - ORD("0")]);
	ELSE
	  ds[0] := '%'; ds[1] := ch; ds[2] := "";
	  BurgInOut.WriteSmm(ds);	
	END;
      ELSIF ch = "$" THEN
	ch := str[ix]; INC(ix);
	IF (ch >= "0") AND (ch <= "9") THEN
	  BurgInOut.WriteSmm("self");
	  BurgInOut.WriteSmm(lst^.strs[ORD(ch) - ORD("0")]);
	  BurgInOut.WriteSmm("^.$S");
	ELSE
	  ds[0] := '$'; ds[1] := ch; ds[2] := "";
	  BurgInOut.WriteSmm(ds);	
	END;
      ELSE
	BurgInOut.WriteCmm(ch);	
      END;
      ch := str[ix]; INC(ix);
    END;
  END ExpandString;

  PROCEDURE GetHelperList(prod : ProdIndex;
		      VAR list : HelperBlk);

    PROCEDURE Recurse(tree   : Tree;
		      prefix : ARRAY OF CHAR;
		  VAR list   : HelperBlk);
      VAR str : ARRAY [0 .. 127] OF CHAR;
    BEGIN
      IF tree^.isChain THEN
	StdStrings.Assign(prefix,list^.strs[list^.next]); INC(list^.next);
      ELSIF tree^.left <> NIL THEN
	StdStrings.Assign(prefix,str);
	StdStrings.Append("^.$L",str);
	Recurse(tree^.left,str,list);
	IF tree^.right <> NIL THEN
	  StdStrings.Assign(prefix,str);
	  StdStrings.Append("^.$R",str);
	  Recurse(tree^.right,str,list);
        END;
      ELSE (* is a terminal leaf node ... *)
	StdStrings.Assign(prefix,list^.strs[list^.next]); INC(list^.next);
      END;
    END Recurse;

  BEGIN
    NEW(list);
    list^.strs[0] := "";
    list^.next := 1;
    Recurse(prodInfo[prod].rhs,"",list);
  END GetHelperList;

  PROCEDURE GenerateHelpers;

    PROCEDURE EmitHelperCall(tree   : Tree;
			 VAR next   : CARDINAL;
			 VAR list   : HelperBlk);
    BEGIN
      IF tree^.isChain THEN (* a non-terminal leaf *)
        BurgInOut.WriteSmm("    rHelp[self");
        BurgInOut.WriteSmm(list^.strs[next]);
        BurgInOut.WriteSmm("^.$S.rules[");
	WriteNT(tree^.nonTerm);
        BurgInOut.WriteSmm("]](self");
        BurgInOut.WriteSmm(list^.strs[next]);
        BurgInOut.WriteSmm(");");
        BurgInOut.WriteLmm;
	INC(next);
      ELSIF tree^.left <> NIL THEN
	EmitHelperCall(tree^.left,next,list);
	IF tree^.right <> NIL THEN
	  EmitHelperCall(tree^.right,next,list);
	END;
      ELSE (* a terminal leaf *)
	INC(next);
      END;
    END EmitHelperCall;

    VAR index : ProdIndex;
	nextA : CARDINAL;
	bufPos : INTEGER;
	bufLen : CARDINAL;
	buffer : ARRAY [0 .. 255] OF CHAR;

  BEGIN
    BurgInOut.WriteSmm(
    " (* ============== Recursion helper procedures ============= *)");
    BurgInOut.WriteLmm; BurgInOut.WriteLmm;
    FOR index := 1 TO thisProd DO
      nextA := 1;
      BurgInOut.ModProcH(index);
      WITH prodInfo[index] DO
        bufPos := decPos;
	MburgS.SkipAndGetLine(0,decEnd,bufPos,bufLen,buffer);
	WHILE bufLen > 0 DO
          BurgInOut.WriteSmm("    "); 
	  ExpandString(buffer,strings);
	  BurgInOut.WriteLmm; 
	  MburgS.SkipAndGetLine(decCol-1,decEnd,bufPos,bufLen,buffer);
	END;
      END;
      BurgInOut.WriteSmm("  BEGIN"); BurgInOut.WriteLmm;
      EmitProdComment(index,2);
      WITH prodInfo[index] DO
        EmitHelperCall(rhs,nextA,strings);
        bufPos := semPos;
	MburgS.SkipAndGetLine(0,semEnd,bufPos,bufLen,buffer);
	IF bufLen > 0 THEN 
          BurgInOut.WriteSmm("   (* semantic actions follow ... *)"); 
          BurgInOut.WriteLmm; 
	END;
	WHILE bufLen > 0 DO
          BurgInOut.WriteSmm("    "); 
	  ExpandString(buffer,strings);
	  BurgInOut.WriteLmm; 
	  MburgS.SkipAndGetLine(semCol-1,semEnd,bufPos,bufLen,buffer);
	END;
      END;
      BurgInOut.EndProcH(index);
    END;
  END GenerateHelpers;

 (* ================================================================== *)
 (* ===================  Emit Traverse Helpers  ====================== *)
 (* ================================================================== *)

 (* ================================================================== *)

  PROCEDURE WriteIncludes;
    VAR bufPos : INTEGER;
	bufLen : CARDINAL;
	buffer : ARRAY [0 .. 255] OF CHAR;
  BEGIN
    bufPos := inclPos;
    MburgS.SkipAndGetLine(0,inclEnd,bufPos,bufLen,buffer);
    WHILE bufLen > 0 DO
      BurgInOut.WriteCfd(Ascii.ht); 
      BurgInOut.WriteSfd(buffer); 
      BurgInOut.WriteLfd; 
      MburgS.SkipAndGetLine(inclCol-1,inclEnd,bufPos,bufLen,buffer);
    END;
  END WriteIncludes;

  PROCEDURE WriteFormImports;
    VAR bufPos : INTEGER;
	bufLen : CARDINAL;
	buffer : ARRAY [0 .. 255] OF CHAR;
  BEGIN
    bufPos := formPos;
    MburgS.SkipAndGetLine(0,formEnd,bufPos,bufLen,buffer);
    WHILE bufLen > 0 DO
      BurgInOut.WriteSfd("  "); 
      BurgInOut.WriteSfd(buffer); 
      BurgInOut.WriteLfd; 
      MburgS.SkipAndGetLine(formCol-1,formEnd,bufPos,bufLen,buffer);
    END;
    BurgInOut.WriteLfd; 
  END WriteFormImports;

  PROCEDURE WriteStaticActions(term : TermIndex);
    VAR bufPos : INTEGER;
	bufLen : CARDINAL;
	buffer : ARRAY [0 .. 255] OF CHAR;
	curs   : CardSequences.ElemPtr;
	prodI  : CARDINAL;
  BEGIN
    CardSequences.InitCursor(termInfo[term].prodList,curs);
    WHILE NOT CardSequences.Ended(curs) DO
      CardSequences.GetNext(curs,prodI);
      WITH prodInfo[prodI] DO
        bufPos := semPos;
	MburgS.SkipAndGetLine(0,semEnd,bufPos,bufLen,buffer);
	WHILE bufLen > 0 DO
          BurgInOut.WriteSmm("    "); 
	  ExpandString(buffer,strings);
	  BurgInOut.WriteLmm; 
	  MburgS.SkipAndGetLine(semCol-1,semEnd,bufPos,bufLen,buffer);
	END;
      END; (* with *)
    END; (* while *)
  END WriteStaticActions;

 (* ================================================================== *)

  PROCEDURE MakeModBody;
    CONST NL    = BurgInOut.WriteLmm;
    VAR   index : CARDINAL;
          str   : ARRAY [0 .. 127] OF CHAR;
  BEGIN
   (* first, the global information *)
    BurgInOut.WriteSmm(
    " (* ============ Global data and exported procs ============ *)"); NL; NL;
    BurgInOut.WriteSmm("  VAR arity : ARRAY $E OF Types.Card8;"); NL;
    BurgInOut.WriteSmm("      match : ARRAY $E OF PROCEDURE($T);"); NL;
    BurgInOut.WriteSmm("      rHelp : ARRAY ProdIndex OF PROCEDURE($T);");NL;
    IF trace THEN
      BurgInOut.WriteSmm("  VAR traceDepth : CARDINAL;"); BurgInOut.WriteLmm;
    END;
    BurgInOut.WriteSmm("(*");NL;
    BurgInOut.WriteSmm(" *    tHelp : ARRAY ProdIndex OF PROCEDURE($T);");NL;
    BurgInOut.WriteSmm(" *    eHelp : ARRAY ProdIndex OF PROCEDURE($T);");NL;
    BurgInOut.WriteSmm(" *)");NL;NL;
   (* next, the main launching procedures *)
    BurgInOut.WriteSmm("  PROCEDURE LabelTree(self : $T);"); NL;
    BurgInOut.WriteSmm("  BEGIN"); NL;
    BurgInOut.WriteSmm("    match[self^.$O](self);"); NL;
    BurgInOut.WriteSmm("  END LabelTree;"); NL; NL;
    BurgInOut.WriteSmm("  PROCEDURE Reduce(self : $T; goal : FormEnum);"); NL;
    IF trace THEN
      BurgInOut.WriteSmm("  BEGIN"); NL;
      BurgInOut.WriteSmm("    InOut.WriteString('==== Reduce to NT #');"); NL;
      BurgInOut.WriteSmm("    InOut.WriteCard(ORD(goal),0);"); NL;
      BurgInOut.WriteSmm("    InOut.WriteString('==== ');"); NL;
      BurgInOut.WriteSmm("    InOut.WriteLn;"); NL;
      BurgInOut.WriteSmm("    rHelp[self^.$S.rules[goal]](self);"); NL;
      BurgInOut.WriteSmm("  END Reduce;");
    ELSE
      BurgInOut.WriteSmm("  BEGIN rHelp[self^.$S.rules[goal]](self) END Reduce;");
    END;
    NL; NL;
    BurgInOut.WriteSmm("(*"); NL;
    BurgInOut.WriteSmm(" *PROCEDURE Traverse(self : $T; goal : FormEnum);"); NL;
    BurgInOut.WriteSmm(" *BEGIN tHelp[self^.$S.rules[goal]](self) END Traverse;"); NL;
    BurgInOut.WriteSmm(" *"); NL;
    BurgInOut.WriteSmm(" *PROCEDURE Emit(self : $T; goal : FormEnum);"); NL;
    BurgInOut.WriteSmm(" *BEGIN eHelp[self^.$S.rules[goal]](self) END Emit;"); NL;
    BurgInOut.WriteSmm(" *)"); NL; NL;

    BurgInOut.WriteSmm(
    " (* ============= Table initialization codes =============== *)"); NL; NL;
    BurgInOut.WriteSmm("BEGIN (* $PMatch *)"); NL;
    FOR index := 1 TO maxT DO
      IF termInfo[index].termArity >= 0 THEN
        BurgInOut.WriteSmm("  arity["); WriteT(index);
        BurgInOut.WriteSmm("] := "); WritePI(termInfo[index].termArity); 
        BurgInOut.WriteCmm(";"); NL;
      END;
    END;
    FOR index := 1 TO maxT DO
      BurgInOut.WriteSmm("  match["); WriteT(index);
      BurgInOut.WriteSmm("] := "); WriteT(index);
      BurgInOut.WriteSmm("Match;"); NL;
    END;
    FOR index := 1 TO thisProd DO
      BurgInOut.WriteSmm("  rHelp["); WritePI(index);
      BurgInOut.WriteSmm("] := Reduce"); WritePI(index);
      BurgInOut.WriteCmm(";"); NL;
    END;
    IF trace THEN 
      BurgInOut.WriteSmm("  traceDepth := 0;");
    END;
   (* ================================================================== *)
    WriteFormImports;

    BurgInOut.WriteSfd("  TYPE"); BurgInOut.WriteLfd;
    BurgInOut.WriteSfd("    ProdIndex = [0 .. ");
    BurgInOut.WriteCfd(CHR(ORD('0') + thisProd DIV 64));
    BurgInOut.WriteCfd(CHR(ORD('0') + thisProd DIV 8 MOD 8));
    BurgInOut.WriteCfd(CHR(ORD('0') + thisProd MOD 8));
    BurgInOut.WriteSfd("B];"); BurgInOut.WriteLfd; BurgInOut.WriteLfd; 

    BurgInOut.WriteSfd("    FormEnum = (errFrm,");
    FOR index := 1 TO ntTide DO
      MburgS.GetString(nonTermI[index].pos,nonTermI[index].len,str);
      BurgInOut.WriteSfd(str);
      IF index <> ntTide THEN BurgInOut.WriteCfd(",") END;
      IF index MOD 8 = 0 THEN 
	BurgInOut.WriteLfd; BurgInOut.WriteCfd(Ascii.ht); 
      END;
    END;
    BurgInOut.WriteSfd(");"); BurgInOut.WriteLfd; BurgInOut.WriteLfd;
    BurgInOut.WriteSfd("    CostType  = ARRAY FormEnum OF Card16;"); 
    BurgInOut.WriteLfd;
    BurgInOut.WriteSfd("    ProdType  = ARRAY FormEnum OF ProdIndex;"); 
    BurgInOut.WriteLfd;
    BurgInOut.WriteSfd("    StateType = "); BurgInOut.WriteLfd; 
    BurgInOut.WriteSfd("      RECORD"); BurgInOut.WriteLfd; 
    BurgInOut.WriteSfd("	costs : CostType;"); BurgInOut.WriteLfd; 
    BurgInOut.WriteSfd("	rules : ProdType;"); BurgInOut.WriteLfd; 
    WriteIncludes;
    BurgInOut.WriteSfd("      END;"); BurgInOut.WriteLfd; BurgInOut.WriteLfd;
  END MakeModBody;

BEGIN
  FOR index := 0 TO MAX(TermIndex) DO
    termInfo[index].termArity := unknown;
    CardSequences.InitSequence(termInfo[index].prodList);
  END;
  nonTermI[0].reached := FALSE;
  CardSequences.InitSequence(nonTermI[0].chainSeq);
  CardSequences.InitSequence(nonTermI[0].prodIdxs);
  ntTide   := 0;
  thisProd := 0;
  goalSmbl := 1;
END BurgAst.
