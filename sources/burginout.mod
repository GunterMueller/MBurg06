(*
 *  This program is copyright (c) 1995 Faculty of Information Technology,
 *  Queensland University of Technology, Brisbane, Australia.
 *  The program may be freely distributed in source or compiled form,
 *  provided this copyright notice remains intact in the sources. 
 *  Original program, June 1995, John Gough.
 *
 *  Support module for Mburg
 *  (original kjg 29-April-1995)
 *)
IMPLEMENTATION MODULE BurgInOut;

IMPORT 
	SYSTEM, Ascii, Storage, ProgArgs, GpFiles, MburgS,
	StdStrings, TextInOut, InOut, StdError, UxFiles;

  CONST crlf      = Ascii.lf; (* DOS == Ascii.cr + Ascii.lf *)
	verstring = "# Mburg generator-generator version 0.5, ";
		   (* VERSION STRING MUST BE UPDATED MANUALLY *)

(* ============================== utilities ============================= *)

  PROCEDURE TitleMessage;
    VAR local : ARRAY [0 .. 31] OF CHAR;
  BEGIN
    ProgArgs.VersionTime(local);
    InOut.WriteString(verstring); 
    InOut.WriteString(local); 
  END TitleMessage;

  PROCEDURE ErrorMessage(p : ARRAY OF CHAR;
			 m : ARRAY OF CHAR;
			 s : ARRAY OF CHAR);
  BEGIN
    StdError.WriteString("# Mburg: ");
    StdError.WriteString(p); StdError.Write(" "); StdError.Write("<");
    StdError.WriteString(m); StdError.Write(">"); StdError.Write(" ");
    StdError.WriteString(s); StdError.WriteLn;
  END ErrorMessage;
 
(* ---------------------------------------------------------------------- *)

  PROCEDURE IdErrorMessage(p : ARRAY OF CHAR;
			   pos,len : INTEGER;
			   s : ARRAY OF CHAR);
    VAR str : ARRAY [0 .. 63] OF CHAR;
  BEGIN
    MburgS.GetString(pos,len,str);
    ErrorMessage(p,str,s);
  END IdErrorMessage;
 
(* ---------------------------------------------------------------------- *)

  PROCEDURE InfoMessage(p : ARRAY OF CHAR;
			m : ARRAY OF CHAR;
			s : ARRAY OF CHAR);
  BEGIN
    InOut.WriteString("# Mburg: ");
    InOut.WriteString(p); InOut.Write(" "); InOut.Write("<");
    InOut.WriteString(m); InOut.Write(">"); InOut.Write(" ");
    InOut.WriteString(s); InOut.WriteLn;
  END InfoMessage;
 
(* ---------------------------------------------------------------------- *)

  PROCEDURE CrdMessage (p : ARRAY OF CHAR;
			m : CARDINAL;
			s : ARRAY OF CHAR);
  BEGIN
    InOut.WriteString("# Mburg: ");
    InOut.WriteString(p); InOut.Write(" "); InOut.Write("<");
    InOut.WriteCard(m,0); InOut.Write(">"); InOut.Write(" ");
    InOut.WriteString(s); InOut.WriteLn;
  END CrdMessage;
 
(* ---------------------------------------------------------------------- *)

  PROCEDURE WriteUsage();
    VAR local : ARRAY [0 .. 30] OF CHAR;
  BEGIN
    TitleMessage;
    InOut.WriteString(
        "# Mburg usage: mburg [options] filename<cr>" + crlf
      + "# Options ---" + crlf
      + "#	-p ident	-- use ident as name prefix" + crlf
      + "#	-v              -- verbose mode" + crlf
      + "#	-t              -- emit tracing code" + crlf
      + "# Input is <filename[.brg]>" + crlf
      + "# Output files are ---" + crlf
      + "#	[prefix]Match.(def,mod)" + crlf
      + "#	[prefix]FormDefs.(def,mod)" + crlf);
  END WriteUsage;
 
(* ---------------------------------------------------------------------- *)

  VAR
    argument,
    sourceArg, 
    sourceName, 
    lstName, 
    matchName,
    formName,
    dummy,
    prefix      : ARRAY [0 .. 127] OF CHAR;

  VAR
    newExp,
    operExp,
    enumExp,
    leftExp,
    rightExp,
    stateExp,
    modNmExp,
    typNmExp    : ARRAY [0 .. 64] OF CHAR;

  VAR 
    sourceBrg,
    matchMod, 
    matchDef, 
    formDef, 
    formMod     : UxFiles.File;
    okay        : BOOLEAN;

  PROCEDURE BadOption;
  BEGIN
    ErrorMessage("Warning, bad option",argument,"");
  END BadOption;

  PROCEDURE ParseArgs;
    VAR next, argN : CARDINAL;
  BEGIN
    next := 1;
    trace := FALSE;
    verbose := FALSE;
    prefix[0] := "";
    argN := ProgArgs.ArgNumber();
    (* check on correct parameter usage *)
    IF ProgArgs.ArgNumber() < 2 THEN WriteUsage; HALT END;
    ProgArgs.GetArg(1,argument); INC(next);
    WHILE argument[0] = "-" DO
      CASE CAP(argument[1]) OF
      | "P" : IF argN <= next THEN WriteUsage; HALT END;
	      ProgArgs.GetArg(next,prefix); INC(next);
      | "V" : verbose := TRUE;
	      TitleMessage;
      | "T" : trace := TRUE;
      ELSE    BadOption;
      END;
      IF argN <= next THEN WriteUsage; HALT END;
      ProgArgs.GetArg(next,argument); INC(next);
    END;
    sourceArg := argument;
   (* should have next = argN *)
    IF next < argN THEN
      ErrorMessage("Warning, args after",sourceArg,"ignored");
    END;
  END ParseArgs;

  PROCEDURE OpenFiles(VAR src,lst : UxFiles.File);
  BEGIN
    GpFiles.GpFindLocal(sourceArg,"brg",sourceName,src);
    IF src = NIL THEN
      ErrorMessage("Could not open input file",sourceArg,"[.brg]");
      HALT;
    END;
    (* open the output file for the source listing (* Scanner.lst *) *)
    GpFiles.GpCreateFile(sourceArg,"lst",lstName,lst);
    IF lst = NIL THEN
      ErrorMessage("Could not create input file",sourceArg,"[.lst]");
      HALT;
    END;
  END OpenFiles;
 
  PROCEDURE CloseFile(lst : UxFiles.File);
  BEGIN 
    UxFiles.Close(lst,okay);
  END CloseFile;

  PROCEDURE CloseMatchFiles;
  BEGIN
    UxFiles.Close(matchMod,okay);
    UxFiles.Close(matchDef,okay);
    UxFiles.Close(formMod,okay);
    UxFiles.Close(formDef,okay);
  END CloseMatchFiles;

  PROCEDURE OpenMatchFiles;
  BEGIN
    matchName := prefix;
    StdStrings.Append("Match",matchName);
    GpFiles.GpCreateFile(matchName,"mod",dummy,matchMod);
    IF matchMod = NIL THEN
      ErrorMessage("Could not create matcher file",matchName,"[.mod]");
      HALT;
    ELSIF verbose THEN
      InfoMessage('creating matcher file',dummy,'');
    END;
    GpFiles.GpCreateFile(matchName,"def",dummy,matchDef);
    IF matchMod = NIL THEN
      ErrorMessage("Could not create matcher file",matchName,"[.def]");
      HALT;
    ELSIF verbose THEN
      InfoMessage('creating matcher file',dummy,'');
    END;
    formName := prefix;
    StdStrings.Append("FormDefs",formName);
    GpFiles.GpCreateFile(formName,"mod",dummy,formMod);
    IF formMod = NIL THEN
      ErrorMessage("Could not create formdefs file",formName,"[.mod]");
      HALT;
    ELSIF verbose THEN
      InfoMessage('creating formdefs file',dummy,'');
    END;
    GpFiles.GpCreateFile(formName,"def",dummy,formDef);
    IF formDef = NIL THEN
      ErrorMessage("Could not create formdefs file",formName,"[.def]");
      HALT;
    ELSIF verbose THEN
      InfoMessage('creating formdefs file',dummy,'');
    END;
  END OpenMatchFiles;

 (* ======================== match write procs ========================= *)
 
  CONST W = TextInOut.WriteString;
	L = TextInOut.WriteLn;
	C = TextInOut.Write;

  PROCEDURE GetOpS;
  BEGIN
    MburgS.GetString(MburgS.pos+1,MburgS.len-2,operExp);
  END GetOpS;

  PROCEDURE GetNewS;
  BEGIN
    MburgS.GetString(MburgS.pos+1,MburgS.len-2,newExp);
  END GetNewS;

  PROCEDURE GetEnumS;
  BEGIN
    MburgS.GetString(MburgS.pos+1,MburgS.len-2,enumExp);
  END GetEnumS;

  PROCEDURE GetLeftS;
  BEGIN
    MburgS.GetString(MburgS.pos+1,MburgS.len-2,leftExp);
  END GetLeftS;

  PROCEDURE GetRightS;
  BEGIN
    MburgS.GetString(MburgS.pos+1,MburgS.len-2,rightExp);
  END GetRightS;

  PROCEDURE GetStateS;
  BEGIN
    MburgS.GetString(MburgS.pos+1,MburgS.len-2,stateExp);
  END GetStateS;

  PROCEDURE GetMnameS;
  BEGIN
    MburgS.GetString(MburgS.pos+1,MburgS.len-2,modNmExp);
  END GetMnameS;

  PROCEDURE GetTnameS;
  BEGIN
    MburgS.GetString(MburgS.pos+1,MburgS.len-2,typNmExp);
  END GetTnameS;

  PROCEDURE WriteExp(fil : UxFiles.File;
		 VAR str : ARRAY OF CHAR);
    VAR ch : CHAR;
	ix : CARDINAL;
	in : CARDINAL;
  BEGIN
    ch := str[0]; ix := 0;
    WHILE ch <> "" DO
      IF ch = "$" THEN
	INC(ix); ch := str[ix];
        CASE ch OF
	| "E" : TextInOut.WriteString(fil,enumExp);
	| "L" : TextInOut.WriteString(fil,leftExp);
	| "M" : TextInOut.WriteString(fil,modNmExp);
	| "N" : TextInOut.WriteString(fil,newExp);
		IF newExp[0] <> "" THEN 
		  TextInOut.Write(fil,";"); 
		  TextInOut.WriteLn(fil);
		  FOR in := 2 TO ix DO TextInOut.Write(fil," ") END;
		END;
	| "O" : TextInOut.WriteString(fil,operExp);
	| "P" : TextInOut.WriteString(fil,prefix);
	| "R" : TextInOut.WriteString(fil,rightExp);
	| "S" : TextInOut.WriteString(fil,stateExp);
	| "T" : TextInOut.WriteString(fil,typNmExp);
	ELSE 
	  TextInOut.Write(fil,ch);
	END;
      ELSE
        TextInOut.Write(fil,ch);
      END;
      INC(ix); ch := str[ix];
    END;
  END WriteExp;

  PROCEDURE WriteSmm(str : ARRAY OF CHAR);
  BEGIN
    WriteExp(matchMod,str);
  END WriteSmm;

  PROCEDURE WriteSmd(str : ARRAY OF CHAR);	(* emitstr to match def *)
  BEGIN
    WriteExp(matchDef,str);
  END WriteSmd;

  PROCEDURE WriteSfm(str : ARRAY OF CHAR);	(* emitstr to form mod  *)
  BEGIN
    WriteExp(formMod,str);
  END WriteSfm;

  PROCEDURE WriteSfd(str : ARRAY OF CHAR);	(* emitstr to form def  *)
  BEGIN
    WriteExp(formDef,str);
  END WriteSfd;

  PROCEDURE WriteCmm(chr : CHAR);
  BEGIN
    TextInOut.Write(matchMod,chr);
  END WriteCmm;

  PROCEDURE WriteCmd(chr : CHAR);
  BEGIN
    TextInOut.Write(matchDef,chr);
  END WriteCmd;

  PROCEDURE WriteCfm(chr : CHAR);
  BEGIN
    TextInOut.Write(formMod,chr);
  END WriteCfm;

  PROCEDURE WriteCfd(chr : CHAR);
  BEGIN
    TextInOut.Write(formDef,chr);
  END WriteCfd;

  PROCEDURE WriteLmm();
  BEGIN
    TextInOut.WriteLn(matchMod);
  END WriteLmm;

  PROCEDURE WriteLmd();
  BEGIN
    TextInOut.WriteLn(matchDef);
  END WriteLmd;

  PROCEDURE WriteLfm();
  BEGIN
    TextInOut.WriteLn(formMod);
  END WriteLfm;

  PROCEDURE WriteLfd();
  BEGIN
    TextInOut.WriteLn(formDef);
  END WriteLfd;

  PROCEDURE WriteMatchHeaders;
    VAR   M : UxFiles.File;
  BEGIN
  (* -------------------------------------------------------------------- *)
    M := matchDef;
    W(M,"(*"); L(M);
    W(M," *  File automatically produced by Mburg from grammar <");
    W(M,sourceName); C(M,">"); L(M);
    W(M," *)"); L(M);

    W(M,"DEFINITION MODULE "); W(M,matchName); C(M,";"); L(M);
    WriteSmd("  IMPORT Types;"); L(M);
    WriteSmd("  FROM $PFormDefs IMPORT FormEnum;"); L(M);
    WriteSmd("  FROM $M IMPORT $T;"); L(M); L(M);
    WriteSmd("  CONST max = MAX(Types.Card16);"); L(M); L(M);
    WriteSmd("  PROCEDURE LabelTree (root : $T);"); L(M);
    WriteSmd("  PROCEDURE Reduce    (root : $T; goal : FormEnum);"); L(M);
    WriteSmd("(*"); L(M);
    WriteSmd(" *PROCEDURE Traverse  (root : $T; goal : FormEnum);"); L(M);
    WriteSmd(" *PROCEDURE Emit      (root : $T; goal : FormEnum);"); L(M);
    WriteSmd(" *)"); L(M); L(M);
  (* -------------------------------------------------------------------- *)
    M := matchMod;
    W(M,"(*"); L(M);
    W(M," *  File automatically produced by Mburg from grammar <");
    W(M,sourceName); C(M,">"); L(M);
    W(M," *)"); L(M);

    WriteSmm("IMPLEMENTATION MODULE "); W(M,matchName); C(M,";"); L(M);
    WriteSmm("  IMPORT SYSTEM, Types;"); L(M);
    WriteSmm(
    "  FROM $PFormDefs IMPORT FormEnum, CostType, ProdType, ProdIndex;"); L(M);
    WriteSmm("  FROM $M IMPORT $T, $E;"); L(M);
    IF trace THEN
      WriteSmm("  IMPORT InOut;"); L(M); 
    END;
    L(M);
  (* -------------------------------------------------------------------- *)
    M := formDef;
    W(M,"(*"); L(M);
    W(M," *  File automatically produced by Mburg from grammar <");
    W(M,sourceName); C(M,">"); L(M);
    W(M," *)"); L(M);

    W(M,"DEFINITION MODULE "); W(M,formName); C(M,";"); L(M);
    WriteSfd("  FROM Types IMPORT Card16;"); L(M); L(M);
  (* -------------------------------------------------------------------- *)
    M := formMod;
    W(M,"(*"); L(M);
    W(M," *  File automatically produced by Mburg from grammar <");
    W(M,sourceName); C(M,">"); L(M);
    W(M," *)"); L(M);

    WriteSfm("IMPLEMENTATION MODULE "); W(M,formName); C(M,";"); L(M);
    WriteSfm("END "); W(M,formName); C(M,"."); L(M);
  (* -------------------------------------------------------------------- *)
  END WriteMatchHeaders;

  PROCEDURE ModProcM(pos,len : INTEGER);
    VAR   M : UxFiles.File;
    VAR str : ARRAY [0 .. 63] OF CHAR;
  BEGIN
    M := matchMod;
    MburgS.GetString(pos,len,str); (* str[0] := CAP(str[0]); *)
    W(M,"  PROCEDURE "); W(M,str); WriteSmm("Match(self : $T);"); L(M);
    W(M,"    VAR lCost,rCost : Types.Card16;"); L(M);
    IF trace THEN W(M,"        count : CARDINAL;"); L(M) END;
    W(M,"  BEGIN"); L(M);
  END ModProcM;

  PROCEDURE ModProcI(pos,len : INTEGER);
    VAR   M : UxFiles.File;
    VAR str : ARRAY [0 .. 63] OF CHAR;
  BEGIN
    M := matchMod;
    MburgS.GetString(pos,len,str); (* str[0] := CAP(str[0]); *)
    W(M,"  PROCEDURE Insert"); W(M,str); WriteSmm("	(self : $T;"); L(M);
    WriteSmm("			 rule : ProdIndex;"); L(M);
    WriteSmm("			 cost : CARDINAL);"); L(M);
    W(M,"  BEGIN"); L(M);
  END ModProcI;

  PROCEDURE DefProcM(pos,len : INTEGER);
    VAR   M : UxFiles.File;
    VAR str : ARRAY [0 .. 63] OF CHAR;
  BEGIN
    M := matchDef;
    MburgS.GetString(pos,len,str); (* str[0] := CAP(str[0]); *)
    W(M,"  PROCEDURE "); W(M,str); WriteSmd("Match(self : $T);"); L(M); L(M);
  END DefProcM;

  PROCEDURE ModProcH(prod : INTEGER);
    VAR   M : UxFiles.File;
  BEGIN
    M := matchMod;
    W(M,"  PROCEDURE Reduce"); TextInOut.WriteCard(M,prod,0);
    WriteSmm("(self : $T);"); L(M);
  END ModProcH;

  PROCEDURE EndProcM(pos,len : INTEGER);
    VAR   M : UxFiles.File;
    VAR str : ARRAY [0 .. 63] OF CHAR;
  BEGIN
    M := matchMod;
    MburgS.GetString(pos,len,str); (* str[0] := CAP(str[0]); *)
    W(M,"  END "); W(M,str); W(M,"Match;"); L(M); L(M);
  END EndProcM;

  PROCEDURE EndProcI(pos,len : INTEGER);
    VAR   M : UxFiles.File;
    VAR str : ARRAY [0 .. 63] OF CHAR;
  BEGIN
    M := matchMod;
    MburgS.GetString(pos,len,str); (* str[0] := CAP(str[0]); *)
    W(M,"  END "); W(M,"Insert"); W(M,str); C(M,";"); L(M); L(M);
  END EndProcI;

  PROCEDURE EndProcH(prod : INTEGER);
    VAR   M : UxFiles.File;
  BEGIN
    M := matchMod;
    W(M,"  END "); W(M,"Reduce"); 
    TextInOut.WriteCard(M,prod,0); C(M,";"); L(M); L(M);
  END EndProcH;

  PROCEDURE WriteMatchTrailers;
    VAR   M : UxFiles.File;
  BEGIN
    M := matchMod; 
    L(M);
    W(M,"END "); W(M,matchName); C(M,"."); L(M);
    M := matchDef; 
    W(M,"END "); W(M,matchName); C(M,"."); L(M);
    M := formDef; 
    W(M,"END "); W(M,formName); C(M,"."); L(M);
  END WriteMatchTrailers;

  PROCEDURE CopyBlockH;
    VAR count : CARDINAL;
	index : CARDINAL;
	byte  : SYSTEM.BYTE;
  BEGIN
    ProgArgs.Assert(matchMod <> NIL);
    UxFiles.Open(sourceBrg,sourceName,UxFiles.ReadOnly,okay);
    UxFiles.SetPos(sourceBrg,hStart);
    IF hEnd > hStart THEN
      count := hEnd - hStart - 1;
    ELSE
      count := 0;
    END;
    IF verbose THEN CrdMessage('writing header block',count,'bytes') END;
   (*
    * sanity check ...
    *)
    ProgArgs.Assert(count < 1000000, "include too long, or uninitialized");
    FOR index := 0 TO count DO
      UxFiles.ReadByte(sourceBrg,byte); UxFiles.WriteByte(matchMod,byte);
    END;
    TextInOut.WriteLn(matchMod);
    UxFiles.Close(sourceBrg,okay);
  END CopyBlockH;

 (* ======================== end write procs ========================= *)

BEGIN
  operExp  := "op";
  leftExp  := "l";
  rightExp := "r";
  stateExp := "s^";
  modNmExp := "NodeDefs";
  typNmExp := "NodeDesc";
  enumExp  := "OperEnum";
  newExp   := "";
END BurgInOut.
