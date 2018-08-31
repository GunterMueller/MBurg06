
MBURG is a bottom up tree rewriter in the general style of IBURG. It has
a somewhat different implementation, and produces its output in standard
Modula2.

 *  This program and its documentation are both copyright (c) 1995 
 *  Faculty of Information Technology,
 *  Queensland University of Technology, Brisbane, Australia.
 *  The program may be freely distributed in source or compiled form,
 *  provided this copyright notice remains intact in the sources. 
 *  Original program, June 1995, John Gough.

The sources in this directory are sufficient to create mburg, provided
you have the gpm version of COCO/R on your system. Failing that, all of
the coco-produced sources which you need are in the subdirectory sources.

One full example of a mburg grammar for an experimental tree rewriter for
SPARC is in the directory test.  The compiler from which it was taken
placed a lot of the semantic actions in a helper module CgHelper. Still
it may give you an idea.

There is a postscript reference manual mburg.ps here, and the short 
announcement of availability sigplan.ps.

Enjoy.

-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
K John Gough                      Internet:     j.gough@qut.edu.au
Professor of Computer Science     VOX:          +61 7 864-2316
Queensland University of Tech.    Fax:          +61 7 864-1282
                                  http://www.dstc.qut.edu.au/~gough/

Automata      _--_|\              Faculty of Information Technology
rules OK     /      QUT           Queensland University of Technology
             \_.--._/             Box 2434  Brisbane 4001  AUSTRALIA
                   v              Phone: +61 7 864-2111

-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-

