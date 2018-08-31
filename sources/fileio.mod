IMPLEMENTATION MODULE FileIO;
(* General file input/output
   Partly based on code by MB 90/11/25; heavily modified
   Gardens Point Modula (UNIX) version by kjg April 1993 *)

IMPORT UxFiles, UxHandles, StdStrings, SYSTEM, TextInOut, StdFiles, Ascii,
	InOut, StdError, GpFiles, SysClock, PathLookup, ProgArgs;

FROM Storage IMPORT
  ALLOCATE, DEALLOCATE;

CONST
  BS       = 10C;
  DEL	   = 177C;
  notImp   = "not implemented in this version";

VAR
  param     : CARDINAL;
  numPar    : CARDINAL;

PROCEDURE NextParameter (VAR s: ARRAY OF CHAR);
  VAR
    i: CARDINAL;
  BEGIN
    IF param < numPar THEN
      ProgArgs.GetArg(param,s);
    ELSE
      s[0] := "";
    END;
    INC(param);
  END NextParameter;

PROCEDURE GetEnv (var: ARRAY OF CHAR; VAR val: ARRAY OF CHAR);
  BEGIN
    ProgArgs.EnvironString(var,val);
  END GetEnv;

PROCEDURE Open (VAR f: File; filename: ARRAY OF CHAR; output: BOOLEAN);
  VAR
    i:    CARDINAL;
    ch :  CHAR;
    name: ARRAY [0 .. 12] OF CHAR;
    outName: ARRAY [0 .. 131] OF CHAR;
  BEGIN
    ExtractFileName(filename, name);
    IF (name[0] = 0C) OR 
	(StdStrings.Compare(name, "CON") = StdStrings.equal) THEN
      (* con already opened, but reset it *)
      Okay := TRUE; f := StdFiles.StreamOfStdIn(); 
      REPEAT UxFiles.ReadByte(f,ch) UNTIL ch = ">";
      RETURN
    ELSIF StdStrings.Compare(name, "ERR") = StdStrings.equal THEN
      Okay := TRUE; f := StdFiles.StreamOfStdErr(); RETURN
    ELSIF output THEN
      GpFiles.GpCreateFile(filename,"",outName,f);
      Okay := f <> NIL;
    ELSE
      GpFiles.GpFindLocal(filename,"",outName,f);
      Okay := f <> NIL;
    END;
(*
 *  IF Okay THEN
 *    InOut.WriteString(outName);
 *    InOut.Write(">");
 *  ELSE
 *    InOut.WriteString(filename);
 *    InOut.WriteString("> failed");
 *  END;
 *  InOut.WriteLn;
 *) 
  END Open;

PROCEDURE Flush(f : File);
  BEGIN
    UxHandles.FlushStream(f,Okay);
  END Flush;

PROCEDURE Close (VAR f: File);
  BEGIN
    UxFiles.Close(f,Okay);
    f := NIL;
  END Close;

PROCEDURE Delete (VAR f : File);
  BEGIN
    ProgArgs.Assert(FALSE,notImp);
    (* UxFiles wants a filename! *)
  END Delete;

PROCEDURE SearchFile (VAR f: File; env, name: ARRAY OF CHAR; output: BOOLEAN);
  VAR
    fname : ARRAY [0 .. 63]   OF CHAR;
    path  : ARRAY [0 .. 1023] OF CHAR;
  BEGIN
    ProgArgs.EnvironString(env,path);
(*
 *  InOut.WriteString("Using ");
 *  InOut.WriteString(env);
 *  InOut.WriteString("=");
 *  InOut.WriteString(path);
 *  InOut.WriteLn();
 *)
    GpFiles.GpFindOnPath(path, name, "", fname, f);
    IF output THEN (* Find... opens for reading *)
      UxFiles.Close(f,Okay);
      UxFiles.Open(f,fname,UxFiles.WriteOnly,Okay);
    ELSE
      Okay := f <> NIL;
    END;
(*
 *  IF Okay THEN
 *    InOut.WriteString(fname);
 *    InOut.Write(">");
 *  ELSE
 *    InOut.WriteString(name);
 *    InOut.WriteString(": ");
 *    InOut.WriteString(env);
 *    InOut.Write("=");
 *    InOut.WriteString(path);
 *    InOut.WriteString("> failed");
 *  END;
 *  InOut.WriteLn;
 *)
  END SearchFile;

PROCEDURE ExtractDirectory (fullName: ARRAY OF CHAR;
                            VAR directory: ARRAY OF CHAR);
  VAR
    i, start: CARDINAL;
  BEGIN
    start := 0; i := 0;
    WHILE (i <= HIGH(fullName)) AND (fullName[i] # 0C) DO
      IF i <= HIGH(directory) THEN
        directory[i] := fullName[i];
      END;
      IF (fullName[i] = ":") OR (fullName[i] = "/") THEN start := i + 1 END;
      INC(i)
    END;
    IF start <= HIGH(directory) THEN directory[start] := 0C END
  END ExtractDirectory;

PROCEDURE ExtractFileName (fullName: ARRAY OF CHAR;
                           VAR filename: ARRAY OF CHAR);
  VAR
    i, l, start: CARDINAL;
  BEGIN
    start := 0; l := 0;
    WHILE (l <= HIGH(fullName)) AND (fullName[l] # 0C) DO
      IF (fullName[l] = ":") OR (fullName[l] = "/") THEN start := l + 1 END;
      INC(l)
    END;
    i := 0;
    WHILE (start < l) AND (i <= HIGH(filename)) DO
      filename[i] := (fullName[start]); INC(start); INC(i)
    END;
    IF i <= HIGH(filename) THEN filename[i] := 0C END
  END ExtractFileName;

PROCEDURE AppendExtension (old, ext: ARRAY OF CHAR; VAR new: ARRAY OF CHAR);
  CONST max = 65;
  VAR
    i, j: CARDINAL;
    fn:   ARRAY [0 .. max] OF CHAR;
  BEGIN
    ExtractDirectory(old, new);
    ExtractFileName(old, fn);
    i := 0; j := 0;
    WHILE (i <= max) AND (fn[i] # 0C) DO
      fn[i] := (fn[i]); IF fn[i] = "." THEN j := i + 1 END;
      INC(i)
    END;
    IF (j # i) (* then name did not end with "." *) OR (i = 0) THEN
      IF j # 0 THEN i := j - 1 END;
      IF (ext[0] # ".") AND (ext[0] # 0C) THEN
        IF i <= max THEN fn[i] := "."; INC(i) END
      END;
      j := 0;
      WHILE (j <= HIGH(ext)) AND (ext[j] # 0C) AND (i <= max) DO
        fn[i] := (ext[j]); INC(i); INC(j)
      END
    END;
    IF i <= max THEN fn[i] := 0C END;
    StdStrings.Append(fn, new);
  END AppendExtension;

PROCEDURE ChangeExtension (old, ext: ARRAY OF CHAR; VAR new: ARRAY OF CHAR);
  CONST max = 65;
  VAR
    i, j: CARDINAL;
    fn:   ARRAY [0 .. max] OF CHAR;
  BEGIN
    ExtractDirectory(old, new);
    ExtractFileName(old, fn);
    i := 0; j := 0;
    WHILE (i <= max) AND (fn[i] # 0C) DO
      fn[i] := (fn[i]); IF (fn[i] = ".") THEN j := i + 1 END;
      INC(i)
    END;
    IF j # 0 THEN i := j - 1 END;
    IF (ext[0] # ".") AND (ext[0] # 0C) THEN
      IF i <= max THEN fn[i] := "."; INC(i) END
    END;
    j := 0;
    WHILE (j <= HIGH(ext)) AND (ext[j] # 0C) AND (i <= max) DO
      fn[i] := (ext[j]); INC(i); INC(j)
    END;
    IF i <= max THEN fn[i] := 0C END;
    StdStrings.Append(fn, new)
  END ChangeExtension;

PROCEDURE Length (f: File): INTEGER;
  BEGIN
    IF f = NIL THEN 
      Okay := FALSE; RETURN VAL(INTEGER, 0);
    ELSE
      Okay := TRUE;  RETURN StdFiles.Length(f);
    END;
  END Length;

PROCEDURE GetPos (f: File): INTEGER;
  VAR
    high: CARDINAL;
  BEGIN
    IF f = NIL THEN Okay := FALSE; RETURN VAL(INTEGER, 0) END;
    UxFiles.GetPos(f,high);
    RETURN VAL(INTEGER,high);
  END GetPos;

PROCEDURE SetPos (f: File; pos: INTEGER);
  VAR
    high, low: CARDINAL;
  BEGIN
    IF f = NIL THEN Okay := FALSE; RETURN END;
    UxFiles.SetPos(f,pos)
  END SetPos;

PROCEDURE Reset (f : File);
  BEGIN
    IF f = NIL THEN
      Okay := FALSE
    ELSE
      UxFiles.Reset(f);
    END
  END Reset;

PROCEDURE Rewrite (f : File);
  BEGIN
    IF f = NIL THEN
      Okay := FALSE
    ELSE
      UxFiles.Reset(f);	(* ??? *)
    END
  END Rewrite;

PROCEDURE EndOfLine (f: File): BOOLEAN;
  BEGIN
    IF (f = NIL) 
      THEN Okay := FALSE; RETURN TRUE
      ELSE Okay := TRUE;  (* and crash *)
         ProgArgs.Assert(FALSE);
    END
  END EndOfLine;

PROCEDURE EndOfFile (f: File): BOOLEAN;
  BEGIN
    IF f = NIL 
      THEN Okay := FALSE; RETURN TRUE
      ELSE 
	Okay := TRUE; 
	RETURN UxFiles.EndFile(f);
    END
  END EndOfFile;

PROCEDURE Read (f: File; VAR ch: CHAR);
  BEGIN
    IF f = NIL THEN
      Okay := FALSE; ch := 0C; RETURN
    END;
    UxFiles.ReadByte(f,ch);
    IF (ch = 377C) AND UxFiles.EndFile(f) THEN 
      ch   := 0C; Okay := FALSE;
    END;
  END Read;

PROCEDURE ReadAgain (f: File);
  BEGIN
    ProgArgs.Assert(FALSE,notImp);
  END ReadAgain;

PROCEDURE ReadLn (f: File);
  VAR
    ch: CHAR;
  BEGIN
    IF f = NIL THEN
      Okay := FALSE; RETURN
    END;
    REPEAT UxFiles.ReadByte(f,ch);
    UNTIL (ch = EOL) OR (ch = 377C) AND UxFiles.EndFile(f);
  END ReadLn;

PROCEDURE ReadString (f: File; VAR str: ARRAY OF CHAR);
  BEGIN
    TextInOut.ReadString(f,str);
    Okay := str[0] <> "";
  END ReadString;

PROCEDURE ReadLine (f: File; VAR str: ARRAY OF CHAR);
  VAR
    j:  CARDINAL;
    ch: CHAR;
  BEGIN
    str[0] := 0C; j := 0;
    IF f = NIL THEN
      Okay := FALSE; RETURN
    END;
    Read(f, ch);
    IF Okay THEN
      WHILE ch >= " " DO
        IF j <= HIGH(str) THEN str[j] := ch END; INC(j);
        Read(f, ch);
        WHILE (ch = BS) OR (ch = DEL) DO 
		IF j > 0 THEN DEC(j) END; Read(f, ch) END
      END;
      IF j <= HIGH(str) THEN str[j] := 0C END;
      Okay := j > 0;
    END
  END ReadLine;

PROCEDURE ReadToken (f: File; VAR str: ARRAY OF CHAR);
  VAR
    j:  CARDINAL;
    ch: CHAR;
  BEGIN
    str[0] := 0C; j := 0;
    IF f = NIL THEN
      Okay := FALSE; RETURN
    END;
    REPEAT Read(f, ch) UNTIL (ch > " ") OR NOT Okay;
    IF Okay THEN
      WHILE ch > " " DO
        IF j <= HIGH(str) THEN str[j] := ch END; INC(j);
        Read(f, ch);
        WHILE (ch = BS) OR (ch = DEL) DO 
		IF j > 0 THEN DEC(j) END; Read(f, ch) END
      END;
      IF j <= HIGH(str) THEN str[j] := 0C END;
      Okay := j > 0;
    END
  END ReadToken;

PROCEDURE ReadInt (f: File; VAR i: INTEGER);
  BEGIN
    TextInOut.ReadInt(f,i);
    Okay := TextInOut.Done;
  END ReadInt;

PROCEDURE ReadCard (f: File; VAR i: CARDINAL);
  BEGIN
    TextInOut.ReadCard(f,i);
    Okay := TextInOut.Done;
  END ReadCard;

PROCEDURE ReadBytes (f: File; VAR buf: ARRAY OF SYSTEM.BYTE; VAR len: CARDINAL);
  BEGIN
    IF f = NIL
      THEN
        Okay := FALSE; len := 0;
      ELSE
        UxFiles.ReadNBytes(f, SYSTEM.ADR(buf), len, len);
        Okay := len <> 0;
    END;
  END ReadBytes;

PROCEDURE Write (f: File; ch: CHAR);
  BEGIN
    TextInOut.Write(f,ch);
  END Write;

PROCEDURE WriteLn (f: File);
    VAR dummy : BOOLEAN;
  BEGIN
    TextInOut.WriteLn(f);
  END WriteLn;

PROCEDURE WriteString (f: File; str: ARRAY OF CHAR);
    VAR dummy : BOOLEAN;
  BEGIN
    IF f = con THEN Flush(f) END;
    TextInOut.WriteString(f,str);
  END WriteString;

PROCEDURE WriteText (f: File; text: ARRAY OF CHAR; len: INTEGER);
  VAR
    i, slen: INTEGER;
    dummy : BOOLEAN;
  BEGIN
    slen := LENGTH(text);
    FOR i := 0 TO len - 1 DO
      IF i < slen THEN Write(f, text[i]) ELSE Write(f, " ") END;
    END;
  END WriteText;

PROCEDURE WriteInt (f: File; n: INTEGER; w: CARDINAL);
  BEGIN
    TextInOut.WriteInt(f,n,w);
  END WriteInt;

PROCEDURE WriteCard (f: File; n, w: CARDINAL);
  BEGIN
    TextInOut.WriteCard(f,n,w);
  END WriteCard;

PROCEDURE WriteBytes (f: File; VAR buf: ARRAY OF SYSTEM.BYTE; len: CARDINAL);
    VAR num : CARDINAL;
  BEGIN
    UxFiles.WriteNBytes(f, SYSTEM.ADR(buf), len, num);
    Okay := num = len;
  END WriteBytes;

PROCEDURE GetDate (VAR Year, Month, Day: CARDINAL);
  VAR
    time : SysClock.DateTime;
  BEGIN
    SysClock.GetClock(time);
    Year  := time.year;
    Month := time.month;
    Day   := time.day;
  END GetDate;

PROCEDURE GetTime (VAR Hrs, Mins, Secs, Hsecs: CARDINAL);
  VAR
    time : SysClock.DateTime;
  BEGIN
    SysClock.GetClock(time);
    Hrs   := time.hour;
    Mins  := time.minute;
    Secs  := time.second;
    Hsecs := time.fractions;
  END GetTime;

PROCEDURE Write2 (f: File; i: CARDINAL);
  BEGIN
    Write(f, CHR(i DIV 10 + ORD("0")));
    Write(f, CHR(i MOD 10 + ORD("0")));
  END Write2;

PROCEDURE WriteDate (f: File);
  VAR
    Year, Month, Day: CARDINAL;
  BEGIN
    IF f = NIL THEN
      Okay := FALSE; RETURN
    END;
    GetDate(Year, Month, Day);
    Write2(f, Day); Write(f, "/"); Write2(f, Month); Write(f, "/");
    WriteCard(f, Year, 0)
  END WriteDate;

PROCEDURE WriteTime (f: File);
  VAR
    Hrs, Mins, Secs, Hsecs: CARDINAL;
  BEGIN
    IF f = NIL THEN
      Okay := FALSE; RETURN
    END;
    GetTime(Hrs, Mins, Secs, Hsecs);
    Write2(f, Hrs); Write(f, ":"); Write2(f, Mins); Write(f, ":");
    Write2(f, Secs)
  END WriteTime;

VAR
  Hrs0, Mins0, Secs0, Hsecs0: CARDINAL;
  Hrs1, Mins1, Secs1, Hsecs1: CARDINAL;

PROCEDURE WriteElapsedTime (f: File);
  VAR
    Hrs, Mins, Secs, Hsecs, s, hs: CARDINAL;
  BEGIN
    IF f = NIL THEN
      Okay := FALSE; RETURN
    END;
    GetTime(Hrs, Mins, Secs, Hsecs);
    WriteString(f, "Elapsed time : ");
    s := (Hrs - Hrs1) * 3600 + (Mins - Mins1) * 60 + Secs - Secs1;
    IF Hsecs >= Hsecs1
      THEN hs := Hsecs - Hsecs1
      ELSE hs := (Hsecs + 100) - Hsecs1; DEC(s);
    END;
    WriteCard(f, s, 0); Write(f, ".");
    Write2(f, hs); WriteString(f, " s"); WriteLn(f);
    Hrs1 := Hrs; Mins1 := Mins; Secs1 := Secs; Hsecs1 := Hsecs;
  END WriteElapsedTime;

PROCEDURE WriteExecutionTime (f: File);
  VAR
    Hrs, Mins, Secs, Hsecs, s, hs: CARDINAL;
  BEGIN
    IF f = NIL THEN
      Okay := FALSE; RETURN
    END;
    GetTime(Hrs, Mins, Secs, Hsecs);
    WriteString(f, "Execution time : ");
    s := (Hrs - Hrs0) * 3600 + (Mins - Mins0) * 60 + Secs - Secs0;
    IF Hsecs >= Hsecs0
      THEN hs := Hsecs - Hsecs0
      ELSE hs := (Hsecs + 100) - Hsecs0; DEC(s);
    END;
    WriteCard(f, s, 0); Write(f, "."); Write2(f, hs);
    WriteString(f, " s"); WriteLn(f);
  END WriteExecutionTime;

BEGIN
  GetTime(Hrs0, Mins0, Secs0, Hsecs0);
  Hrs1 := Hrs0; Mins1 := Mins0; Secs1 := Secs0; Hsecs1 := Hsecs0;
  param := 1;
  numPar := ProgArgs.ArgNumber();
  err := StdFiles.StreamOfStdErr();
  UxFiles.Open(con,"/dev/tty",UxFiles.ReadWrite,Okay);
END FileIO.
