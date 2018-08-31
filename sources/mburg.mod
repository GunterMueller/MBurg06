MODULE Mburg;
(* 
 *  This is the main module for Mburg.
 *  The auxiliary modules <Grammar>S (scanner) and <Grammar>P (parser)
 *  are assumed to have been constructed with COCO/R compiler generator.
 *  (original kjg 29-April-1995)
 *)

  FROM MburgS IMPORT lst, src, errors, Error, CharAt;
  FROM MburgP IMPORT Parse;
  IMPORT 
	BurgAst, BurgInOut, SYSTEM, Ascii, Storage, 
	TextInOut, InOut, StdError;

  MODULE ListHandler;
  (* ------------------- Source Listing and Error handler -------------- *)
    IMPORT Storage, SYSTEM;
    IMPORT TextInOut; 
    IMPORT lst, CharAt, errors;
    EXPORT StoreError, PrintListing;

    TYPE
      Err = POINTER TO ErrDesc;
      ErrDesc = RECORD
        nr, line, col: INTEGER;
        next: Err
      END;

    VAR
      firstErr, lastErr: Err;

    PROCEDURE StoreError (nr, line, col: INTEGER; pos: INTEGER);
    (* Store an error message for later printing *)
      VAR
        nextErr: Err;
      BEGIN
        Storage.ALLOCATE(nextErr, SYSTEM.TSIZE(ErrDesc));
        nextErr^.nr := nr; nextErr^.line := line; nextErr^.col := col;
        nextErr^.next := NIL;
        IF firstErr = NIL
          THEN firstErr := nextErr
          ELSE lastErr^.next := nextErr
        END;
        lastErr := nextErr;
        INC(errors)
      END StoreError;

    PROCEDURE GetLine (VAR pos  : INTEGER;
                       VAR line : ARRAY OF CHAR;
                       VAR eof  : BOOLEAN);
    (* Read a source line. Return empty line if eof *)
      CONST
        cr = 15C;
        lf = 12C;
        tab = 11C;
        endF = 0C;
      VAR
        ch: CHAR;
        i:  CARDINAL;
      BEGIN
        ch := CharAt(pos); INC(pos);
        i := 0; eof := FALSE;
        WHILE (ch # lf) & (ch # endF) DO     (* lf == eol in UNIX *) 
     (* WHILE (ch # cr) & (ch # endF) DO     (* cr,lf in DOS *) *)
          IF ch = tab THEN ch := ' ' END;
          line[i] := ch; INC(i);                      (* UNIX *) 
     (*   IF ch # lf THEN line[i] := ch; INC(i) END;  (* DOS *) *)
          ch := CharAt(pos); INC(pos);
        END;
        eof := (i = 0) & (ch = endF); line[i] := 0C;
      END GetLine;

    PROCEDURE PrintErr (nr, col: INTEGER);
    (* Print an error message *)

      PROCEDURE Msg (s: ARRAY OF CHAR);
        BEGIN
          TextInOut.WriteString(lst, s)
        END Msg;

      PROCEDURE Skp (index : INTEGER);
        BEGIN
          WHILE index > 0 DO
            TextInOut.Write(lst, " "); DEC(index);
          END;
        END Skp;
 
      BEGIN
        TextInOut.WriteString(lst, "*****");
	Skp(col);
        TextInOut.WriteString(lst, "^ ");
        CASE nr OF
	   0: Msg("EOF expected")
	|  1: Msg("identifier expected")
	|  2: Msg("number expected")
	|  3: Msg("string expected")
	|  4: Msg("'HEADER' expected")
	|  5: Msg("'DECLARATIONS' expected")
	|  6: Msg("'RULES' expected")
	|  7: Msg("'ENDRULES' expected")
	|  8: Msg("'%start' expected")
	|  9: Msg("'%OP' expected")
	| 10: Msg("'%NEW' expected")
	| 11: Msg("'%ENUM' expected")
	| 12: Msg("'%LEFT' expected")
	| 13: Msg("'%RIGHT' expected")
	| 14: Msg("'%STATE' expected")
	| 15: Msg("'%MNAME' expected")
	| 16: Msg("'%TNAME' expected")
	| 17: Msg("'%ATTR' expected")
	| 18: Msg("'<' expected")
	| 19: Msg("'>' expected")
	| 20: Msg("'%FORM' expected")
	| 21: Msg("'%term' expected")
	| 22: Msg("'=' expected")
	| 23: Msg("'.' expected")
	| 24: Msg("'(.' expected")
	| 25: Msg("'.)' expected")
	| 26: Msg("'(' expected")
	| 27: Msg("',' expected")
	| 28: Msg("')' expected")
	| 29: Msg("'&' expected")
	| 30: Msg("not expected")
	| 31: Msg("error in SemAction")
	| 32: Msg("error in Cost")
	| 33: Msg("error in PredFunc")
	| 34: Msg("error in Tree")
	| 35: Msg("error in Tree")
	| 36: Msg("error in Declaration")
        ELSE Msg("Error: "); TextInOut.WriteInt(lst, nr, 0);
        END;
        TextInOut.WriteLn(lst)
      END PrintErr;

    PROCEDURE PrintListing;
    (* Print a source listing with error messages *)
      VAR
        nextErr:   Err;
        eof:       BOOLEAN;
        lnr, errC: INTEGER;
        srcPos:    INTEGER;
        line:      ARRAY [0 .. 255] OF CHAR;
      BEGIN
        TextInOut.WriteString(lst, "Listing:");
        TextInOut.WriteLn(lst); TextInOut.WriteLn(lst);
        srcPos := 0; nextErr := firstErr;
        GetLine(srcPos, line, eof); lnr := 1; errC := 0;
        WHILE ~ eof DO
          TextInOut.WriteInt(lst, lnr, 5); TextInOut.WriteString(lst, "  ");
          TextInOut.WriteString(lst, line); TextInOut.WriteLn(lst);
          WHILE (nextErr # NIL) & (nextErr^.line = lnr) DO
            PrintErr(nextErr^.nr, nextErr^.col); INC(errC);
            nextErr := nextErr^.next
          END;
          GetLine(srcPos, line, eof); INC(lnr);
        END;
        IF nextErr # NIL THEN
          TextInOut.WriteInt(lst, lnr, 5); TextInOut.WriteLn(lst);
          WHILE nextErr # NIL DO
            PrintErr(nextErr^.nr, nextErr^.col); INC(errC);
            nextErr := nextErr^.next
          END
        END;
        TextInOut.WriteLn(lst);
        TextInOut.WriteInt(lst, errC, 5); TextInOut.WriteString(lst, " error");
        IF errC # 1 THEN TextInOut.Write(lst, "s") END;
        TextInOut.WriteLn(lst); TextInOut.WriteLn(lst); TextInOut.WriteLn(lst);
      END PrintListing;

    BEGIN
      firstErr := NIL;
    END ListHandler;

  (* --------------------------- main module ------------------------------- *)

  CONST crlf = Ascii.lf; (* DOS == Ascii.cr + Ascii.lf *)
 
  BEGIN
    BurgInOut.ParseArgs;
    BurgInOut.OpenFiles(src,lst);
    (* install error reporting procedure (* Scanner.Error *) *)
    Error := StoreError;
 
    (* instigate the compilation (* Parser.Parse *) *)
    IF BurgInOut.verbose THEN
      InOut.WriteString('# Mburg: parsing');
      InOut.WriteLn();
    END;
 
    Parse;
    IF errors = 0 THEN
      IF BurgInOut.verbose THEN
        InOut.WriteString('# Mburg: parsed correctly');
        InOut.WriteLn;
      END;
      BurgAst.Check;
    END;
    (* generate the source listing on (* Scanner.lst *) *)
    PrintListing;
    BurgInOut.CloseFile(lst);

    (* examine the outcome from (* Scanner.errors *) *)
    IF errors # 0
      THEN
        StdError.WriteString('Incorrect source');
        StdError.WriteLn;
      ELSE
        BurgInOut.OpenMatchFiles;
        BurgInOut.WriteMatchHeaders;
	BurgInOut.CopyBlockH;

    (* ++++++++ Add further activities if required ++++++++++ *)
        BurgAst.MakeInitializers;
        BurgAst.GenerateMatchers;
        BurgAst.GenerateInserts;
        BurgAst.GenerateHelpers;

        BurgInOut.CloseFile(src);

        BurgAst.MakeModBody;

        BurgInOut.WriteMatchTrailers;
        BurgInOut.CloseMatchFiles;
      END;
  END Mburg.
 
