% This program by D. E. Knuth is not copyrighted and can be used freely.
% Version 0 was completed on April 23, 1984.
% Version 0.1 added char_code output (May 4).
% Version 0.2 included rules and dots in the boundary calculations (May 25).
% Version 0.3 added label type "/" (May 27).
% Version 0.4 (by Arthur Samuel) improved the dot labeling routine (July 23).
% Version 0.5 added the slant font for rules (September 2).
% Version 0.6 changed label types and allowed invisible dots (September 28).
% Version 1.0 switched to new GF format (December 8).
% Version 1.1 switched to newer GF format (February 2, 1985).
% Version 1.2 added the offset operations of MF version 0.8 (April 1, 1985).
% Version 1.3 allowed online entry of gray font, etc. (April 22, 1985).
% Version 1.4 allowed "almost" horizontal or vertical rules (May 20, 1985).
% Version 1.5 corrected a bug in the diagonal slant routine (June 18, 1985).
% Version 1.6 corrected a bug if labels exist but no dots (September 13, 1985).
% Version 1.7 changed from am to cm fonts; fam became ext (October 5, 1985).
% Version 2.0 was tuned up for the METAFONTware report (April, 1989).
% Version 3.0 uses 8-bit codes and extended ligatures (October, 1989).

% Here is TeX material that gets inserted after \input webmac
\def\hang{\hangindent 3em\indent\ignorespaces}
\font\ninerm=cmr9
\let\mc=\ninerm % medium caps for names like SAIL
\def\PASCAL{Pascal}
\font\logo=manfnt % font used for the METAFONT logo
\def\MF{{\logo META}\-{\logo FONT}}
\let\swap=\leftrightarrow

\def\(#1){} % this is used to make section names sort themselves better
\def\9#1{} % this is used for sort keys in the index

\def\title{GF$\,$\lowercase{to}$\,$DVI}
\def\contentspagenumber{301}
\def\topofcontents{\null
  \titlefalse % include headline on the contents page
  \def\rheader{\mainfont\hfil \contentspagenumber}
  \vfill
  \centerline{\titlefont The {\ttitlefont GFtoDVI} processor}
  \vskip 15pt
  \centerline{(Version 3.0, October 1989)}
  \vfill}
\def\botofcontents{\vfill
  \centerline{\hsize 5in\baselineskip9pt
    \vbox{\ninerm\noindent
    The preparation of this report
    was supported in part by the National Science
    Foundation under grants IST-8201926, MCS-8300984, and
    CCR-8610181,
    and by the System Development Foundation. `\TeX' is a
    trademark of the American Mathematical Society.
    `{\logo hijklmnj}\kern1pt' is a trademark of Addison-Wesley
    Publishing Company.}}}
\pageno=\contentspagenumber \advance\pageno by 1

@*Introduction.
The \.{GFtoDVI} utility program reads binary generic font (``\.{GF}'')
files that are produced by font compilers such as \MF, and converts them
into device-independent (``\.{DVI}'') files that can be printed to give
annotated hardcopy proofs of the character shapes. The annotations are
specified by the comparatively simple conventions of plain \MF; i.e.,
there are mechanisms for labeling chosen points and for superimposing
horizontal or vertical rules on the enlarged character shapes.

The purpose of \.{GFtoDVI} is simply to make proof copies; it does not
exhaustively test the validity of a \.{GF} file, nor do its algorithms
much resemble the algorithms that are typically used to prepare font
descriptions for commercial typesetting equipment. Another program,
\.{GFtype}, is available for validity checking; \.{GFtype} also serves
as a model of programs that convert fonts from \.{GF} format to some
other coding scheme.

The |banner| string defined here should be changed whenever \.{GFtoDVI}
gets modified.

@d banner	"This is GFtoDVI, Version 3.0" /*printed when the program starts*/ 

@ This program is written in standard \PASCAL, except where it is necessary
to use extensions; for example, \.{GFtoDVI} must read files whose names
are dynamically specified, and such a task would be impossible in pure \PASCAL.
All places where nonstandard constructions are used have been listed in
the index under ``system dependencies.''
@!@^system dependencies@>

Another exception to standard \PASCAL\ occurs in the
use of default branches in |case| statements; the conventions
of \.{TANGLE}, \.{WEAVE}, etc., have been followed.

@ The main input and output files are not mentioned in the program header,
because their external names
will be determined at run time (e.g., by interpreting the
command line that invokes this program). Error messages and other remarks
are written on the |output| file, which the user may
choose to assign to the terminal if the system permits it.
@^system dependencies@>

The term |print| is used instead of |write| when this program writes on
the |output| file, so that all such output can be easily deflected.

@d print(...) fprintf(output,__VA_ARGS__)
@d print_ln(X,...) fprintf(output,X"\n",##__VA_ARGS__)
@d print_nl(...) { fprintf(output,"\n"); fprintf(output,__VA_ARGS__); }

@p@!
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#define abs(X) ((X)>-(X)?(X):-(X))
#define odd(X) @[X&1@]
#define chr(X) @[(unsigned char)X@]
#define get(file) @[fread(&((file).d),sizeof((file).d),1,(file).f)@]
#define reset(file,name) @[file.f=fopen(name+1,"r"),file.f!=NULL?get(file):0@]
#define rewrite(file,name) @[file.f=fopen(name+1,"w")@]
#define eof(file) @[(file.f==NULL||feof(file.f))@]
#define eoln(file) @[(file.d=='\n'||feof(file.f))@]
#define read(file,x) @[x=file.d,get(file)@]
#define write(file,...) @[fprintf(file.f,__VA_ARGS__)@]
#define read_ln(file) @[do { while (!eoln(file)) get(file); get(file); } while (0)@]

@h

@<Labels in the outer block@>@;
@<Constants in the outer block@>@;
@<Types in the outer block@>@;
@<Globals in the outer block@>@;
void initialize(void) /*this procedure gets things started properly*/ 
  {@+int @!i, @!j, @!m, @!n; /*loop indices for initializations*/ 
  print_ln(banner);@/
  @<Set initial values@>;@/
  } 

@ If the program has to stop prematurely, it goes to the
`|exit(0)|'.

@<Labels...@>=

@ The following parameters can be changed at compile time to extend or
reduce \.{GFtoDVI}'s capacity.

@<Constants...@>=
enum {@+@!max_labels=2000@+}; /*maximum number of labels and dots and rules per character*/ 
enum {@+@!pool_size=10000@+}; /*maximum total length of labels and other strings*/ 
enum {@+@!max_strings=1100@+}; /*maximum number of labels and other strings*/ 
enum {@+@!terminal_line_length=150@+}; /*maximum number of characters input in a single
  line of input from the terminal*/ 
enum {@+@!file_name_size=50@+}; /*a file name shouldn't be longer than this*/ 
enum {@+@!font_mem_size=2000@+}; /*space for font metric data*/ 
enum {@+@!dvi_buf_size=800@+}; /*size of the output buffer; must be a multiple of 8*/ 
enum {@+@!widest_row=8192@+}; /*maximum number of pixels per row*/ 
enum {@+@!lig_lookahead=20@+}; /*size of stack used when inserting ligature characters*/ 

@ Labels are given symbolic names by the following definitions, so that
occasional |goto| statements will be meaningful. We insert the label
`|end|:' just before the `\ignorespaces|} |\unskip' of a procedure in
which we have used the `|goto end|' statement defined below; the label
`|reswitch|' is occasionally used just prior to a |case|
statement in which some cases change the conditions and we wish to branch
to the newly applicable case.  Loops that are set up with the |loop|
construction defined below are commonly exited by going to `|done|' or to
`|found|' or to `|not_found|', and they are sometimes repeated by going to
`|resume|'.

Incidentally, this program never declares a label that isn't actually used,
because some fussy \PASCAL\ compilers will complain about redundant labels.

@ Here are some macros for common programming idioms.

@d incr(X)	X=X+1 /*increase a variable by unity*/ 
@d decr(X)	X=X-1 /*decrease a variable by unity*/ 
@d loop	@+while (true) @+ /*repeat over and over until a |goto| happens*/ 
@f loop else
   /*\.{WEB}'s |else| acts like `\ignorespaces|while true do|\unskip'*/ 
@d do_nothing	 /*empty statement*/ 
@ If the \.{GF} file is badly malformed, the whole process must be aborted;
\.{GFtoDVI} will give up, after issuing an error message about the symptoms
that were noticed.

Such errors might be discovered inside of subroutines inside of subroutines,
so a procedure called |jump_out| has been introduced. This procedure, which
simply transfers control to the label |exit(0)| at the end of the program,
contains the only non-local |goto| statement in \.{GFtoDVI}.
@^system dependencies@>

@d abort(...)	@+{@+print(" "__VA_ARGS__);jump_out();@+}
@d bad_gf(X)	abort("Bad GF file: "X"! (at byte %d)", cur_loc-1)
@.Bad GF file@>

@p void jump_out(void)
{@+exit(1);
} 

@ As in \TeX\ and \MF, this program deals with numeric quantities that
are integer multiples of~$2^{16}$, and calls them |scaled|.

@d unity	0200000 /*|scaled| representation of 1.0*/ 

@<Types ...@>=
typedef int scaled; /*fixed-point numbers*/ 

@*The character set.
Like all programs written with the  \.{WEB} system, \.{GFtoDVI} can be
used with any character set. But it uses ASCII code internally, because
the programming for portable input-output is easier when a fixed internal
code is used. Furthermore, both \.{GF} and \.{DVI} files use ASCII code
for file names and certain other strings.
The next few sections of \.{GFtoDVI} have therefore been copied from the
analogous ones in the \.{WEB} system routines.

@<Types ...@>=
typedef uint8_t ASCII_code; /*eight-bit numbers, a subrange of the integers*/ 

@ The original \PASCAL\ compiler was designed in the late 60s, when
six-bit character sets were common, so it did not make provision for lowercase
letters. Nowadays, of course, we need to deal with both capital and
small letters in a convenient way.  So we shall assume that the
\PASCAL\ system being used for \.{GFtoDVI} has a character set containing
at least the standard visible ASCII characters (|'!'| through |'~'|). If
additional characters are present, \.{GFtoDVI} can be configured to
work with them too.

Some \PASCAL\ compilers use the original name |unsigned char| for the data type
associated with the characters in text files, while other \PASCAL s
consider |unsigned char| to be a 64-element subrange of a larger data type that has
some other name.  In order to accommodate this difference, we shall use
the name |text_char| to stand for the data type of the characters in the
output file.  We shall also assume that |text_char| consists of
the elements |chr(first_text_char)| through |chr(last_text_char)|,
inclusive. The following definitions should be adjusted if necessary.
@^system dependencies@>

@d text_char	unsigned char /*the data type of characters in text files*/ 
@d first_text_char	0 /*ordinal number of the smallest element of |text_char|*/ 
@d last_text_char	255 /*ordinal number of the largest element of |text_char|*/ 

@<Types ...@>=
typedef struct {@+FILE *f;@+text_char@,d;@+} text_file;

@ The \.{GFtoDVI} processor converts between ASCII code and
the user's external character set by means of arrays |xord| and |xchr|
that are analogous to \PASCAL's |ord| and |chr| functions.

@<Globals...@>=
ASCII_code @!xord[256];
   /*specifies conversion of input characters*/ 
uint8_t @!xchr[256];
   /*specifies conversion of output characters*/ 

@ Under our assumption that the visible characters of standard ASCII are
all present, the following assignment statements initialize the
|xchr| array properly, without needing any system-dependent changes.

@<Set init...@>=
xchr[040]= ' ' ;
xchr[041]= '!' ;
xchr[042]= '"' ;
xchr[043]= '#' ;
xchr[044]= '$' ;
xchr[045]= '%' ;
xchr[046]= '&' ;
xchr[047]= '\'' ;@/
xchr[050]= '(' ;
xchr[051]= ')' ;
xchr[052]= '*' ;
xchr[053]= '+' ;
xchr[054]= ',' ;
xchr[055]= '-' ;
xchr[056]= '.' ;
xchr[057]= '/' ;@/
xchr[060]= '0' ;
xchr[061]= '1' ;
xchr[062]= '2' ;
xchr[063]= '3' ;
xchr[064]= '4' ;
xchr[065]= '5' ;
xchr[066]= '6' ;
xchr[067]= '7' ;@/
xchr[070]= '8' ;
xchr[071]= '9' ;
xchr[072]= ':' ;
xchr[073]= ';' ;
xchr[074]= '<' ;
xchr[075]= '=' ;
xchr[076]= '>' ;
xchr[077]= '?' ;@/
xchr[0100]= '@@' ;
xchr[0101]= 'A' ;
xchr[0102]= 'B' ;
xchr[0103]= 'C' ;
xchr[0104]= 'D' ;
xchr[0105]= 'E' ;
xchr[0106]= 'F' ;
xchr[0107]= 'G' ;@/
xchr[0110]= 'H' ;
xchr[0111]= 'I' ;
xchr[0112]= 'J' ;
xchr[0113]= 'K' ;
xchr[0114]= 'L' ;
xchr[0115]= 'M' ;
xchr[0116]= 'N' ;
xchr[0117]= 'O' ;@/
xchr[0120]= 'P' ;
xchr[0121]= 'Q' ;
xchr[0122]= 'R' ;
xchr[0123]= 'S' ;
xchr[0124]= 'T' ;
xchr[0125]= 'U' ;
xchr[0126]= 'V' ;
xchr[0127]= 'W' ;@/
xchr[0130]= 'X' ;
xchr[0131]= 'Y' ;
xchr[0132]= 'Z' ;
xchr[0133]= '[' ;
xchr[0134]= '\\' ;
xchr[0135]= ']' ;
xchr[0136]= '^' ;
xchr[0137]= '_' ;@/
xchr[0140]= '`' ;
xchr[0141]= 'a' ;
xchr[0142]= 'b' ;
xchr[0143]= 'c' ;
xchr[0144]= 'd' ;
xchr[0145]= 'e' ;
xchr[0146]= 'f' ;
xchr[0147]= 'g' ;@/
xchr[0150]= 'h' ;
xchr[0151]= 'i' ;
xchr[0152]= 'j' ;
xchr[0153]= 'k' ;
xchr[0154]= 'l' ;
xchr[0155]= 'm' ;
xchr[0156]= 'n' ;
xchr[0157]= 'o' ;@/
xchr[0160]= 'p' ;
xchr[0161]= 'q' ;
xchr[0162]= 'r' ;
xchr[0163]= 's' ;
xchr[0164]= 't' ;
xchr[0165]= 'u' ;
xchr[0166]= 'v' ;
xchr[0167]= 'w' ;@/
xchr[0170]= 'x' ;
xchr[0171]= 'y' ;
xchr[0172]= 'z' ;
xchr[0173]= '{' ;
xchr[0174]= '|' ;
xchr[0175]= '}' ;
xchr[0176]= '~' ;

@ Here now is the system-dependent part of the character set.
If \.{GFtoDVI} is being implemented on a garden-variety \PASCAL\ for which
only standard ASCII codes will appear in the input and output files, you
don't need to make any changes here. But if you have, for example, an extended
character set like the one in Appendix~C of {\sl The \TeX book}, the first
line of code in this module should be changed to
$$\hbox{|for i=0 to 037 do xchr[i]=chr(i);|}$$
\.{WEB}'s character set is essentially identical to \TeX's.
@^system dependencies@>

@<Set init...@>=
for (i=0; i<=037; i++) xchr[i]= '?' ;
for (i=0177; i<=0377; i++) xchr[i]= '?' ;

@ The following system-independent code makes the |xord| array contain a
suitable inverse to the information in |xchr|.

@<Set init...@>=
for (i=first_text_char; i<=last_text_char; i++) xord[chr(i)]=' ';
for (i=1; i<=0377; i++) xord[xchr[i]]=i;
xord[ '?' ]='?';

@ The |input_ln| routine waits for the user to type a line at his or her
terminal; then it puts ASCII-code equivalents for the characters on that line
into the |buffer| array. The |term_in| file is used for terminal input.
@^system dependencies@>

Since the terminal is being used for both input and output, some systems
need a special routine to make sure that the user can see a prompt message
before waiting for input based on that message. (Otherwise the message
may just be sitting in a hidden buffer somewhere, and the user will have
no idea what the program is waiting for.) We shall call a system-dependent
subroutine |update_terminal| in order to avoid this problem.

@d update_terminal	fflush(output) /*empty the terminal output buffer*/

@<Glob...@>=
uint8_t @!buffer[terminal_line_length+1];
text_file @!term_in; /*the terminal, considered as an input file*/ 
FILE *output;

@ A global variable |line_length| records the first buffer position after
the line just read.
@^system dependencies@>

@p void input_ln(void) /*inputs a line from the terminal*/ 
{@+update_terminal;if(!term_in.f)term_in.f=stdin,get(term_in);
if (eoln(term_in)) read_ln(term_in);
line_length=0;
while ((line_length < terminal_line_length)&&!eoln(term_in)) 
  {@+buffer[line_length]=xord[term_in.d];incr(line_length);get(term_in);
  } 
} 

@ The global variable |buf_ptr| is used while scanning each line of input;
it points to the first unread character in |buffer|.

@<Glob...@>=
uint8_t @!buf_ptr; /*the number of characters read*/ 
uint8_t @!line_length; /*end of line read by |input_ln|*/ 

@*Device-independent file format.
Before we get into the details of \.{GFtoDVI}, we need to know exactly
what \.{DVI} files are. The form of such files was designed by David R.
@^Fuchs, David Raymond@>
Fuchs in 1979. Almost any reasonable typesetting device can be driven by
a program that takes \.{DVI} files as input, and dozens of such
\.{DVI}-to-whatever programs have been written. Thus, it is possible to
print the output of document compilers like \TeX\ on many different kinds
of equipment. (The following material has been copied almost verbatim from the
program for \TeX.)

A \.{DVI} file is a stream of 8-bit bytes, which may be regarded as a
series of commands in a machine-like language. The first byte of each command
is the operation code, and this code is followed by zero or more bytes
that provide parameters to the command. The parameters themselves may consist
of several consecutive bytes; for example, the `|set_rule|' command has two
parameters, each of which is four bytes long. Parameters are usually
regarded as nonnegative integers; but four-byte-long parameters,
and shorter parameters that denote distances, can be
either positive or negative. Such parameters are given in two's complement
notation. For example, a two-byte-long distance parameter has a value between
$-2^{15}$ and $2^{15}-1$.
@.DVI {\rm files}@>

Incidentally, when two or more 8-bit bytes are combined to form an integer of
16 or more bits, the most significant bytes appear first in the file.
This is called BigEndian order.
@^BigEndian order@>

A \.{DVI} file consists of a ``preamble,'' followed by a sequence of one
or more ``pages,'' followed by a ``postamble.'' The preamble is simply a
|pre| command, with its parameters that define the dimensions used in the
file; this must come first.  Each ``page'' consists of a |bop| command,
followed by any number of other commands that tell where characters are to
be placed on a physical page, followed by an |eop| command. The pages
appear in the order that they were generated, not in any particular
numerical order. If we ignore |nop| commands and \\{fnt\_def} commands
(which are allowed between any two commands in the file), each |eop|
command is immediately followed by a |bop| command, or by a |post|
command; in the latter case, there are no more pages in the file, and the
remaining bytes form the postamble.  Further details about the postamble
will be explained later.

Some parameters in \.{DVI} commands are ``pointers.'' These are four-byte
quantities that give the location number of some other byte in the file;
the first byte is number~0, then comes number~1, and so on. For example,
one of the parameters of a |bop| command points to the previous |bop|;
this makes it feasible to read the pages in backwards order, in case the
results are being directed to a device that stacks its output face up.
Suppose the preamble of a \.{DVI} file occupies bytes 0 to 99. Now if the
first page occupies bytes 100 to 999, say, and if the second
page occupies bytes 1000 to 1999, then the |bop| that starts in byte 1000
points to 100 and the |bop| that starts in byte 2000 points to 1000. (The
very first |bop|, i.e., the one that starts in byte 100, has a pointer of $-1$.)

@ The \.{DVI} format is intended to be both compact and easily interpreted
by a machine. Compactness is achieved by making most of the information
implicit instead of explicit. When a \.{DVI}-reading program reads the
commands for a page, it keeps track of several quantities: (a)~The current
font |f| is an integer; this value is changed only
by \\{fnt} and \\{fnt\_num} commands. (b)~The current position on the page
is given by two numbers called the horizontal and vertical coordinates,
|h| and |v|. Both coordinates are zero at the upper left corner of the page;
moving to the right corresponds to increasing the horizontal coordinate, and
moving down corresponds to increasing the vertical coordinate. Thus, the
coordinates are essentially Cartesian, except that vertical directions are
flipped; the Cartesian version of |(h, v)| would be |(h,-v)|.  (c)~The
current spacing amounts are given by four numbers |w|, |x|, |y|, and |z|,
where |w| and~|x| are used for horizontal spacing and where |y| and~|z|
are used for vertical spacing. (d)~There is a stack containing
|(h, v, w, x, y, z)| values; the \.{DVI} commands |push| and |pop| are used to
change the current level of operation. Note that the current font~|f| is
not pushed and popped; the stack contains only information about
positioning.

The values of |h|, |v|, |w|, |x|, |y|, and |z| are signed integers having up
to 32 bits, including the sign. Since they represent physical distances,
there is a small unit of measurement such that increasing |h| by~1 means
moving a certain tiny distance to the right. The actual unit of
measurement is variable, as explained below.

@ Here is a list of all the commands that may appear in a \.{DVI} file. Each
command is specified by its symbolic name (e.g., |bop|), its opcode byte
(e.g., 139), and its parameters (if any). The parameters are followed
by a bracketed number telling how many bytes they occupy; for example,
`|p[4]|' means that parameter |p| is four bytes long.

\yskip\hang|set_char_0| 0. Typeset character number~0 from font~|f|
such that the reference point of the character is at |(h, v)|. Then
increase |h| by the width of that character. Note that a character may
have zero or negative width, so one cannot be sure that |h| will advance
after this command; but |h| usually does increase.

\yskip\hang|set_char_1| through |set_char_127| (opcodes 1 to 127).
Do the operations of |set_char_0|; but use the character whose number
matches the opcode, instead of character~0.

\yskip\hang|set1| 128 |c[1]|. Same as |set_char_0|, except that character
number~|c| is typeset. \TeX82 uses this command for characters in the
range |128 <= c < 256|.

\yskip\hang|set2| 129 |c[2]|. Same as |set1|, except that |c|~is two
bytes long, so it is in the range |0 <= c < 65536|.

\yskip\hang|set3| 130 |c[3]|. Same as |set1|, except that |c|~is three
bytes long, so it can be as large as $2^{24}-1$. Not even the Chinese
language has this many characters, but this command might prove useful
in some yet unforeseen way.

\yskip\hang|set4| 131 |c[4]|. Same as |set1|, except that |c|~is four
bytes long, possibly even negative. Imagine that.

\yskip\hang|set_rule| 132 |a[4]| |b[4]|. Typeset a solid black rectangle
of height |a| and width |b|, with its bottom left corner at |(h, v)|. Then
set |h=h+b|. If either |a <= 0| or |b <= 0|, nothing should be typeset. Note
that if |b < 0|, the value of |h| will decrease even though nothing else happens.

\yskip\hang|put1| 133 |c[1]|. Typeset character number~|c| from font~|f|
such that the reference point of the character is at |(h, v)|. (The `put'
commands are exactly like the `set' commands, except that they simply put out a
character or a rule without moving the reference point afterwards.)

\yskip\hang|put2| 134 |c[2]|. Same as |set2|, except that |h| is not changed.

\yskip\hang|put3| 135 |c[3]|. Same as |set3|, except that |h| is not changed.

\yskip\hang|put4| 136 |c[4]|. Same as |set4|, except that |h| is not changed.

\yskip\hang|put_rule| 137 |a[4]| |b[4]|. Same as |set_rule|, except that
|h| is not changed.

\yskip\hang|nop| 138. No operation, do nothing. Any number of |nop|'s
may occur between \.{DVI} commands, but a |nop| cannot be inserted between
a command and its parameters or between two parameters.

\yskip\hang|bop| 139 $c_0[4]$ $c_1[4]$ $\ldots$ $c_9[4]$ $p[4]$. Beginning
of a page: Set |(h, v, w, x, y, z)=(0, 0, 0, 0, 0, 0)| and set the stack empty. Set
the current font |f| to an undefined value.  The ten $c_i$ parameters can
be used to identify pages, if a user wants to print only part of a \.{DVI}
file; \TeX82 gives them the values of \.{\\count0} $\ldots$ \.{\\count9}
at the time \.{\\shipout} was invoked for this page.  The parameter |p|
points to the previous |bop| command in the file, where the first |bop|
has $p=-1$.

\yskip\hang|eop| 140.  End of page: Print what you have read since the
previous |bop|. At this point the stack should be empty. (The \.{DVI}-reading
programs that drive most output devices will have kept a buffer of the
material that appears on the page that has just ended. This material is
largely, but not entirely, in order by |v| coordinate and (for fixed |v|) by
|h|~coordinate; so it usually needs to be sorted into some order that is
appropriate for the device in question. \.{GFtoDVI} does not do such sorting.)

\yskip\hang|push| 141. Push the current values of |(h, v, w, x, y, z)| onto the
top of the stack; do not change any of these values. Note that |f| is
not pushed.

\yskip\hang|pop| 142. Pop the top six values off of the stack and assign
them to |(h, v, w, x, y, z)|. The number of pops should never exceed the number
of pushes, since it would be highly embarrassing if the stack were empty
at the time of a |pop| command.

\yskip\hang|right1| 143 |b[1]|. Set |h=h+b|, i.e., move right |b| units.
The parameter is a signed number in two's complement notation, |-128 <= b < 128|;
if |b < 0|, the reference point actually moves left.

\yskip\hang|right2| 144 |b[2]|. Same as |right1|, except that |b| is a
two-byte quantity in the range |-32768 <= b < 32768|.

\yskip\hang|right3| 145 |b[3]|. Same as |right1|, except that |b| is a
three-byte quantity in the range |@t$-2^{23}$@> <= b < @t$2^{23}$@>|.

\yskip\hang|right4| 146 |b[4]|. Same as |right1|, except that |b| is a
four-byte quantity in the range |@t$-2^{31}$@> <= b < @t$2^{31}$@>|.

\yskip\hang|w0| 147. Set |h=h+w|; i.e., move right |w| units. With luck,
this parameterless command will usually suffice, because the same kind of motion
will occur several times in succession; the following commands explain how
|w| gets particular values.

\yskip\hang|w1| 148 |b[1]|. Set |w=b| and |h=h+b|. The value of |b| is a
signed quantity in two's complement notation, |-128 <= b < 128|. This command
changes the current |w|~spacing and moves right by |b|.

\yskip\hang|w2| 149 |b[2]|. Same as |w1|, but |b| is a two-byte-long
parameter, |-32768 <= b < 32768|.

\yskip\hang|w3| 150 |b[3]|. Same as |w1|, but |b| is a three-byte-long
parameter, |@t$-2^{23}$@> <= b < @t$2^{23}$@>|.

\yskip\hang|w4| 151 |b[4]|. Same as |w1|, but |b| is a four-byte-long
parameter, |@t$-2^{31}$@> <= b < @t$2^{31}$@>|.

\yskip\hang|x0| 152. Set |h=h+x|; i.e., move right |x| units. The `|x|'
commands are like the `|w|' commands except that they involve |x| instead
of |w|.

\yskip\hang|x1| 153 |b[1]|. Set |x=b| and |h=h+b|. The value of |b| is a
signed quantity in two's complement notation, |-128 <= b < 128|. This command
changes the current |x|~spacing and moves right by |b|.

\yskip\hang|x2| 154 |b[2]|. Same as |x1|, but |b| is a two-byte-long
parameter, |-32768 <= b < 32768|.

\yskip\hang|x3| 155 |b[3]|. Same as |x1|, but |b| is a three-byte-long
parameter, |@t$-2^{23}$@> <= b < @t$2^{23}$@>|.

\yskip\hang|x4| 156 |b[4]|. Same as |x1|, but |b| is a four-byte-long
parameter, |@t$-2^{31}$@> <= b < @t$2^{31}$@>|.

\yskip\hang|down1| 157 |a[1]|. Set |v=v+a|, i.e., move down |a| units.
The parameter is a signed number in two's complement notation, |-128 <= a < 128|;
if |a < 0|, the reference point actually moves up.

\yskip\hang|down2| 158 |a[2]|. Same as |down1|, except that |a| is a
two-byte quantity in the range |-32768 <= a < 32768|.

\yskip\hang|down3| 159 |a[3]|. Same as |down1|, except that |a| is a
three-byte quantity in the range |@t$-2^{23}$@> <= a < @t$2^{23}$@>|.

\yskip\hang|down4| 160 |a[4]|. Same as |down1|, except that |a| is a
four-byte quantity in the range |@t$-2^{31}$@> <= a < @t$2^{31}$@>|.

\yskip\hang|y0| 161. Set |v=v+y|; i.e., move down |y| units. With luck,
this parameterless command will usually suffice, because the same kind of motion
will occur several times in succession; the following commands explain how
|y| gets particular values.

\yskip\hang|y1| 162 |a[1]|. Set |y=a| and |v=v+a|. The value of |a| is a
signed quantity in two's complement notation, |-128 <= a < 128|. This command
changes the current |y|~spacing and moves down by |a|.

\yskip\hang|y2| 163 |a[2]|. Same as |y1|, but |a| is a two-byte-long
parameter, |-32768 <= a < 32768|.

\yskip\hang|y3| 164 |a[3]|. Same as |y1|, but |a| is a three-byte-long
parameter, |@t$-2^{23}$@> <= a < @t$2^{23}$@>|.

\yskip\hang|y4| 165 |a[4]|. Same as |y1|, but |a| is a four-byte-long
parameter, |@t$-2^{31}$@> <= a < @t$2^{31}$@>|.

\yskip\hang|z0| 166. Set |v=v+z|; i.e., move down |z| units. The `|z|' commands
are like the `|y|' commands except that they involve |z| instead of |y|.

\yskip\hang|z1| 167 |a[1]|. Set |z=a| and |v=v+a|. The value of |a| is a
signed quantity in two's complement notation, |-128 <= a < 128|. This command
changes the current |z|~spacing and moves down by |a|.

\yskip\hang|z2| 168 |a[2]|. Same as |z1|, but |a| is a two-byte-long
parameter, |-32768 <= a < 32768|.

\yskip\hang|z3| 169 |a[3]|. Same as |z1|, but |a| is a three-byte-long
parameter, |@t$-2^{23}$@> <= a < @t$2^{23}$@>|.

\yskip\hang|z4| 170 |a[4]|. Same as |z1|, but |a| is a four-byte-long
parameter, |@t$-2^{31}$@> <= a < @t$2^{31}$@>|.

\yskip\hang|fnt_num_0| 171. Set |f=0|. Font 0 must previously have been
defined by a \\{fnt\_def} instruction, as explained below.

\yskip\hang|fnt_num_1| through |fnt_num_63| (opcodes 172 to 234). Set
|f=1|, \dots, |f=63|, respectively.

\yskip\hang|fnt1| 235 |k[1]|. Set |f=k|. \TeX82 uses this command for font
numbers in the range |64 <= k < 256|.

\yskip\hang|fnt2| 236 |k[2]|. Same as |fnt1|, except that |k|~is two
bytes long, so it is in the range |0 <= k < 65536|. \TeX82 never generates this
command, but large font numbers may prove useful for specifications of
color or texture, or they may be used for special fonts that have fixed
numbers in some external coding scheme.

\yskip\hang|fnt3| 237 |k[3]|. Same as |fnt1|, except that |k|~is three
bytes long, so it can be as large as $2^{24}-1$.

\yskip\hang|fnt4| 238 |k[4]|. Same as |fnt1|, except that |k|~is four
bytes long; this is for the really big font numbers (and for the negative ones).

\yskip\hang|xxx1| 239 |k[1]| |x[k]|. This command is undefined in
general; it functions as a $(k+2)$-byte |nop| unless special \.{DVI}-reading
programs are being used. \TeX82 generates |xxx1| when a short enough
\.{\\special} appears, setting |k| to the number of bytes being sent. It
is recommended that |x| be a string having the form of a keyword followed
by possible parameters relevant to that keyword.

\yskip\hang|xxx2| 240 |k[2]| |x[k]|. Like |xxx1|, but |0 <= k < 65536|.

\yskip\hang|xxx3| 241 |k[3]| |x[k]|. Like |xxx1|, but |0 <= k < @t$2^{24}$@>|.

\yskip\hang|xxx4| 242 |k[4]| |x[k]|. Like |xxx1|, but |k| can be ridiculously
large. \TeX82 uses |xxx4| when |xxx1| would be incorrect.

\yskip\hang|fnt_def1| 243 |k[1]| |c[4]| |s[4]| |d[4]| |a[1]| |l[1]| |n[a+l]|.
Define font |k|, where |0 <= k < 256|; font definitions will be explained shortly.

\yskip\hang|fnt_def2| 244 |k[2]| |c[4]| |s[4]| |d[4]| |a[1]| |l[1]| |n[a+l]|.
Define font |k|, where |0 <= k < 65536|.

\yskip\hang|fnt_def3| 245 |k[3]| |c[4]| |s[4]| |d[4]| |a[1]| |l[1]| |n[a+l]|.
Define font |k|, where |0 <= k < @t$2^{24}$@>|.

\yskip\hang|fnt_def4| 246 |k[4]| |c[4]| |s[4]| |d[4]| |a[1]| |l[1]| |n[a+l]|.
Define font |k|, where |@t$-2^{31}$@> <= k < @t$2^{31}$@>|.

\yskip\hang|pre| 247 |i[1]| |num[4]| |den[4]| |mag[4]| |k[1]| |x[k]|.
Beginning of the preamble; this must come at the very beginning of the
file. Parameters |i|, |num|, |den|, |mag|, |k|, and |x| are explained below.

\yskip\hang|post| 248. Beginning of the postamble, see below.

\yskip\hang|post_post| 249. Ending of the postamble, see below.

\yskip\noindent Commands 250--255 are undefined at the present time.

@ Only a few of the operation codes above are actually needed by \.{GFtoDVI}.

@d set1	128 /*typeset a character and move right*/ 
@d put_rule	137 /*typeset a rule*/ 
@d bop	139 /*beginning of page*/ 
@d eop	140 /*ending of page*/ 
@d push	141 /*save the current positions*/ 
@d pop	142 /*restore previous positions*/ 
@d right4	146 /*move right*/ 
@d down4	160 /*move down*/ 
@d z0	166 /*move down |z|*/ 
@d z4	170 /*move down and set |z|*/ 
@d fnt_num_0	171 /*set current font to 0*/ 
@d fnt_def1	243 /*define the meaning of a font number*/ 
@d pre	247 /*preamble*/ 
@d post	248 /*postamble beginning*/ 
@d post_post	249 /*postamble ending*/ 

@ The preamble contains basic information about the file as a whole. As
stated above, there are six parameters:
$$\hbox{|@!i[1]| |@!num[4]| |@!den[4]| |@!mag[4]| |@!k[1]| |@!x[k]|.}$$
The |i| byte identifies \.{DVI} format; currently this byte is always set
to~2. (The value |i==3| is currently used for an extended format that
allows a mixture of right-to-left and left-to-right typesetting.
Some day we will set |i==4|, when \.{DVI} format makes another
incompatible change---perhaps in the year 2048.)

The next two parameters, |num| and |den|, are positive integers that define
the units of measurement; they are the numerator and denominator of a
fraction by which all dimensions in the \.{DVI} file could be multiplied
in order to get lengths in units of $10^{-7}$ meters. (For example, there are
exactly 7227 \TeX\ points in 254 centimeters, and \TeX82 works with scaled
points where there are $2^{16}$ sp in a point, so \TeX82 sets |num==25400000|
and $|den|=7227\cdot2^{16}=473628672$.)
@^sp@>

The |mag| parameter is what \TeX82 calls \.{\\mag}, i.e., 1000 times the
desired magnification. The actual fraction by which dimensions are
multiplied is therefore $|mag|\cdot|num|/1000|den|$. Note that if a \TeX\
source document does not call for any `\.{true}' dimensions, and if you
change it only by specifying a different \.{\\mag} setting, the \.{DVI}
file that \TeX\ creates will be completely unchanged except for the value
of |mag| in the preamble and postamble. (Fancy \.{DVI}-reading programs allow
users to override the |mag|~setting when a \.{DVI} file is being printed.)

Finally, |k| and |x| allow the \.{DVI} writer to include a comment, which is not
interpreted further. The length of comment |x| is |k|, where |0 <= k < 256|.

@d dvi_id_byte	2 /*identifies the kind of \.{DVI} files described here*/ 

@ Font definitions for a given font number |k| contain further parameters
$$\hbox{|c[4]| |s[4]| |d[4]| |a[1]| |l[1]| |n[a+l]|.}$$
The four-byte value |c| is the check sum that \TeX\ (or whatever program
generated the \.{DVI} file) found in the \.{TFM} file for this font;
|c| should match the check sum of the font found by programs that read
this \.{DVI} file.
@^check sum@>

Parameter |s| contains a fixed-point scale factor that is applied to the
character widths in font |k|; font dimensions in \.{TFM} files and other
font files are relative to this quantity, which is always positive and
less than $2^{27}$. It is given in the same units as the other dimensions
of the \.{DVI} file.  Parameter |d| is similar to |s|; it is the ``design
size,'' and (like~|s|) it is given in \.{DVI} units. Thus, font |k| is to be
used at $|mag|\cdot s/1000d$ times its normal size.

The remaining part of a font definition gives the external name of the font,
which is an ASCII string of length |a+l|. The number |a| is the length
of the ``area'' or directory, and |l| is the length of the font name itself;
the standard local system font area is supposed to be used when |a==0|.
The |n| field contains the area in its first |a| bytes.

Font definitions must appear before the first use of a particular font number.
Once font |k| is defined, it must not be defined again; however, we
shall see below that font definitions appear in the postamble as well as
in the pages, so in this sense each font number is defined exactly twice,
if at all. Like |nop| commands, font definitions can
appear before the first |bop|, or between an |eop| and a |bop|.

@ The last page in a \.{DVI} file is followed by `|post|'; this command
introduces the postamble, which summarizes important facts that \TeX\ has
accumulated about the file, making it possible to print subsets of the data
with reasonable efficiency. The postamble has the form
$$\vbox{\halign{\hbox{#\hfil}\cr
  |post| |p[4]| |num[4]| |den[4]| |mag[4]| |l[4]| |u[4]| |s[2]| |t[2]|\cr
  $\langle\,$font definitions$\,\rangle$\cr
  |post_post| |q[4]| |i[1]| 223's$[{\G}4]$\cr}}$$
Here |p| is a pointer to the final |bop| in the file. The next three
parameters, |num|, |den|, and |mag|, are duplicates of the quantities that
appeared in the preamble.

Parameters |l| and |u| give respectively the height-plus-depth of the tallest
page and the width of the widest page, in the same units as other dimensions
of the file. These numbers might be used by a \.{DVI}-reading program to
position individual ``pages'' on large sheets of film or paper; however,
the standard convention for output on normal size paper is to position each
page so that the upper left-hand corner is exactly one inch from the left
and the top. Experience has shown that it is unwise to design \.{DVI}-to-printer
software that attempts cleverly to center the output; a fixed position of
the upper left corner is easiest for users to understand and to work with.
Therefore |l| and~|u| are often ignored.

Parameter |s| is the maximum stack depth (i.e., the largest excess of
|push| commands over |pop| commands) needed to process this file. Then
comes |t|, the total number of pages (|bop| commands) present.

The postamble continues with font definitions, which are any number of
\\{fnt\_def} commands as described above, possibly interspersed with |nop|
commands. Each font number that is used in the \.{DVI} file must be defined
exactly twice: Once before it is first selected by a \\{fnt} command, and once
in the postamble.

@ The last part of the postamble, following the |post_post| byte that
signifies the end of the font definitions, contains |q|, a pointer to the
|post| command that started the postamble.  An identification byte, |i|,
comes next; this currently equals~2, as in the preamble.

The |i| byte is followed by four or more bytes that are all equal to
the decimal number 223 (i.e., 0337 in octal). \TeX\ puts out four to seven of
these trailing bytes, until the total length of the file is a multiple of
four bytes, since this works out best on machines that pack four bytes per
word; but any number of 223's is allowed, as long as there are at least four
of them. In effect, 223 is a sort of signature that is added at the very end.
@^Fuchs, David Raymond@>

This curious way to finish off a \.{DVI} file makes it feasible for
\.{DVI}-reading programs to find the postamble first, on most computers,
even though \TeX\ wants to write the postamble last. Most operating
systems permit random access to individual words or bytes of a file, so
the \.{DVI} reader can start at the end and skip backwards over the 223's
until finding the identification byte. Then it can back up four bytes, read
|q|, and move to byte |q| of the file. This byte should, of course,
contain the value 248 (|post|); now the postamble can be read, so the
\.{DVI} reader can discover all the information needed for typesetting the
pages. Note that it is also possible to skip through the \.{DVI} file at
reasonably high speed to locate a particular page, if that proves
desirable. This saves a lot of time, since \.{DVI} files used in production
jobs tend to be large.

Unfortunately, however, standard \PASCAL\ does not include the ability to
@^system dependencies@>
access a random position in a file, or even to determine the length of a file.
Almost all systems nowadays provide the necessary capabilities, so \.{DVI}
format has been designed to work most efficiently with modern operating systems.

@*Generic font file format.
The ``generic font'' (\.{GF}) input files that \.{GFtoDVI} must deal with
have a structure that was inspired by \.{DVI} format, although the
operation codes are quite different in most cases.  The term {\sl
generic\/} indicates that this file format doesn't match the conventions
of any name-brand manufacturer; but it is easy to convert \.{GF} files to
the special format required by almost all digital phototypesetting
equipment. There's a strong analogy between the \.{DVI} files written by
\TeX\ and the \.{GF} files written by \MF; and, in fact, the reader will
notice that many of the paragraphs below are identical to their
counterparts in the description of \.{DVI} already given. The following
description has been lifted almost verbatim from the program for \MF.

A \.{GF} file is a stream of 8-bit bytes that may be
regarded as a series of commands in a machine-like language. The first
byte of each command is the operation code, and this code is followed by
zero or more bytes that provide parameters to the command. The parameters
themselves may consist of several consecutive bytes; for example, the
`|boc|' (beginning of character) command has six parameters, each of
which is four bytes long. Parameters are usually regarded as nonnegative
integers; but four-byte-long parameters can be either positive or
negative, hence they range in value from $-2^{31}$ to $2^{31}-1$.
As in \.{DVI} files, numbers that occupy
more than one byte position appear in BigEndian order,
and negative numbers appear in two's complement notation.

A \.{GF} file consists of a ``preamble,'' followed by a sequence of one or
more ``characters,'' followed by a ``postamble.'' The preamble is simply a
|pre| command, with its parameters that introduce the file; this must come
first.  Each ``character'' consists of a |boc| command, followed by any
number of other commands that specify ``black'' pixels,
followed by an |eoc| command. The characters appear in the order that \MF\
generated them. If we ignore no-op commands (which are allowed between any
two commands in the file), each |eoc| command is immediately followed by a
|boc| command, or by a |post| command; in the latter case, there are no
more characters in the file, and the remaining bytes form the postamble.
Further details about the postamble will be explained later.

Some parameters in \.{GF} commands are ``pointers.'' These are four-byte
quantities that give the location number of some other byte in the file;
the first file byte is number~0, then comes number~1, and so on.

@ The \.{GF} format is intended to be both compact and easily interpreted
by a machine. Compactness is achieved by making most of the information
relative instead of absolute. When a \.{GF}-reading program reads the
commands for a character, it keeps track of two quantities: (a)~the current
column number,~|m|; and (b)~the current row number,~|n|.  These are 32-bit
signed integers, although most actual font formats produced from \.{GF}
files will need to curtail this vast range because of practical
limitations. (\MF\ output will never allow $\vert m\vert$ or $\vert
n\vert$ to get extremely large, but the \.{GF} format tries to be more general.)

How do \.{GF}'s row and column numbers correspond to the conventions
of \TeX\ and \MF? Well, the ``reference point'' of a character, in \TeX's
view, is considered to be at the lower left corner of the pixel in row~0
and column~0. This point is the intersection of the baseline with the left
edge of the type; it corresponds to location $(0,0)$ in \MF\ programs.
Thus the pixel in \.{GF} row~0 and column~0 is \MF's unit square, comprising the
region of the plane whose coordinates both lie between 0 and~1. The
pixel in \.{GF} row~|n| and column~|m| consists of the points whose \MF\
coordinates |(x, y)| satisfy |m <= x <= m+1| and |n <= y <= n+1|.  Negative values of
|m| and~|x| correspond to columns of pixels {\sl left\/} of the reference
point; negative values of |n| and~|y| correspond to rows of pixels {\sl
below\/} the baseline.

Besides |m| and |n|, there's also a third aspect of the current
state, namely the @!|paint_switch|, which is always either \\{black} or
\\{white}. Each \\{paint} command advances |m| by a specified amount~|d|,
and blackens the intervening pixels if |paint_switch==black|; then
the |paint_switch| changes to the opposite state. \.{GF}'s commands are
designed so that |m| will never decrease within a row, and |n| will never
increase within a character; hence there is no way to whiten a pixel that
has been blackened.

@ Here is a list of all the commands that may appear in a \.{GF} file. Each
command is specified by its symbolic name (e.g., |boc|), its opcode byte
(e.g., 67), and its parameters (if any). The parameters are followed
by a bracketed number telling how many bytes they occupy; for example,
`|d[2]|' means that parameter |d| is two bytes long.

\yskip\hang|paint_0| 0. This is a \\{paint} command with |d==0|; it does
nothing but change the |paint_switch| from \\{black} to \\{white} or vice~versa.

\yskip\hang\\{paint\_1} through \\{paint\_63} (opcodes 1 to 63).
These are \\{paint} commands with |d==1| to~63, defined as follows: If
|paint_switch==black|, blacken |d|~pixels of the current row~|n|,
in columns |m| through |m+d-1| inclusive. Then, in any case,
complement the |paint_switch| and advance |m| by~|d|.

\yskip\hang|paint1| 64 |d[1]|. This is a \\{paint} command with a specified
value of~|d|; \MF\ uses it to paint when |64 <= d < 256|.

\yskip\hang|paint2| 65 |d[2]|. Same as |paint1|, but |d|~can be as high
as~65535.

\yskip\hang|paint3| 66 |d[3]|. Same as |paint1|, but |d|~can be as high
as $2^{24}-1$. \MF\ never needs this command, and it is hard to imagine
anybody making practical use of it; surely a more compact encoding will be
desirable when characters can be this large. But the command is there,
anyway, just in case.

\yskip\hang|boc| 67 |c[4]| |p[4]| |min_m[4]| |max_m[4]| |min_n[4]|
|max_n[4]|. Beginning of a character:  Here |c| is the character code, and
|p| points to the previous character beginning (if any) for characters having
this code number modulo 256.  (The pointer |p| is |-1| if there was no
prior character with an equivalent code.) The values of registers |m| and |n|
defined by the instructions that follow for this character must
satisfy |min_m <= m <= max_m| and |min_n <= n <= max_n|.  (The values of |max_m| and
|min_n| need not be the tightest bounds possible.)  When a \.{GF}-reading
program sees a |boc|, it can use |min_m|, |max_m|, |min_n|, and |max_n| to
initialize the bounds of an array. Then it sets |m=min_m|, |n=max_n|, and
|paint_switch=white|.

\yskip\hang|boc1| 68 |c[1]| |@!del_m[1]| |max_m[1]| |@!del_n[1]| |max_n[1]|.
Same as |boc|, but |p| is assumed to be~$-1$; also |del_m==max_m-min_m|
and |del_n==max_n-min_n| are given instead of |min_m| and |min_n|.
The one-byte parameters must be between 0 and 255, inclusive.
\ (This abbreviated |boc| saves 19~bytes per character, in common cases.)

\yskip\hang|eoc| 69. End of character: All pixels blackened so far
constitute the pattern for this character. In particular, a completely
blank character might have |eoc| immediately following |boc|.

\yskip\hang|skip0| 70. Decrease |n| by 1 and set |m=min_m|,
|paint_switch=white|. \ (This finishes one row and begins another,
ready to whiten the leftmost pixel in the new row.)

\yskip\hang|skip1| 71 |d[1]|. Decrease |n| by |d+1|, set |m=min_m|, and set
|paint_switch=white|. This is a way to produce |d| all-white rows.

\yskip\hang|skip2| 72 |d[2]|. Same as |skip1|, but |d| can be as large
as 65535.

\yskip\hang|skip3| 73 |d[3]|. Same as |skip1|, but |d| can be as large
as $2^{24}-1$. \MF\ obviously never needs this command.

\yskip\hang|new_row_0| 74. Decrease |n| by 1 and set |m=min_m|,
|paint_switch=black|. \ (This finishes one row and begins another,
ready to {\sl blacken\/} the leftmost pixel in the new row.)

\yskip\hang|@!new_row_1| through |@!new_row_164| (opcodes 75 to 238). Same as
|new_row_0|, but with |m=min_m+1| through |min_m+164|, respectively.

\yskip\hang|xxx1| 239 |k[1]| |x[k]|. This command is undefined in
general; it functions as a $(k+2)$-byte |no_op| unless special \.{GF}-reading
programs are being used. \MF\ generates \\{xxx} commands when encountering
a \&{special} string; this occurs in the \.{GF} file only between
characters, after the preamble, and before the postamble. However,
\\{xxx} commands might appear within characters,
in \.{GF} files generated by other
processors. It is recommended that |x| be a string having the form of a
keyword followed by possible parameters relevant to that keyword.

\yskip\hang|xxx2| 240 |k[2]| |x[k]|. Like |xxx1|, but |0 <= k < 65536|.

\yskip\hang|xxx3| 241 |k[3]| |x[k]|. Like |xxx1|, but |0 <= k < @t$2^{24}$@>|.
\MF\ uses this when sending a \&{special} string whose length exceeds~255.

\yskip\hang|xxx4| 242 |k[4]| |x[k]|. Like |xxx1|, but |k| can be
ridiculously large; |k| mustn't be negative.

\yskip\hang|yyy| 243 |y[4]|. This command is undefined in general;
it functions as a 5-byte |no_op| unless special \.{GF}-reading programs
are being used. \MF\ puts |scaled| numbers into |yyy|'s, as a
result of \&{numspecial} commands; the intent is to provide numeric
parameters to \\{xxx} commands that immediately precede.

\yskip\hang|no_op| 244. No operation, do nothing. Any number of |no_op|'s
may occur between \.{GF} commands, but a |no_op| cannot be inserted between
a command and its parameters or between two parameters.

\yskip\hang|char_loc| 245 |c[1]| |dx[4]| |dy[4]| |w[4]| |p[4]|.
This command will appear only in the postamble, which will be explained shortly.

\yskip\hang|@!char_loc0| 246 |c[1]| |@!dm[1]| |w[4]| |p[4]|.
Same as |char_loc|, except that |dy| is assumed to be zero, and the value
of~|dx| is taken to be |65536*dm|, where |0 <= dm < 256|.

\yskip\hang|pre| 247 |i[1]| |k[1]| |x[k]|.
Beginning of the preamble; this must come at the very beginning of the
file. Parameter |i| is an identifying number for \.{GF} format, currently
131. The other information is merely commentary; it is not given
special interpretation like \\{xxx} commands are. (Note that \\{xxx}
commands may immediately follow the preamble, before the first |boc|.)

\yskip\hang|post| 248. Beginning of the postamble, see below.

\yskip\hang|post_post| 249. Ending of the postamble, see below.

\yskip\noindent Commands 250--255 are undefined at the present time.

@d gf_id_byte	131 /*identifies the kind of \.{GF} files described here*/ 

@ Here are the opcodes that \.{GFtoDVI} actually refers to.

@d paint_0	0 /*beginning of the \\{paint} commands*/ 
@d paint1	64 /*move right a given number of columns, then
  black${}\swap{}$white*/ 
@d paint2	65 /*ditto, with potentially larger number of columns*/ 
@d paint3	66 /*ditto, with potentially excessive number of columns*/ 
@d boc	67 /*beginning of a character*/ 
@d boc1	68 /*abbreviated |boc|*/ 
@d eoc	69 /*end of a character*/ 
@d skip0	70 /*skip no blank rows*/ 
@d skip1	71 /*skip over blank rows*/ 
@d skip2	72 /*skip over lots of blank rows*/ 
@d skip3	73 /*skip over a huge number of blank rows*/ 
@d new_row_0	74 /*move down one row and then right*/ 
@d xxx1	239 /*for \&{special} strings*/ 
@d xxx2	240 /*for somewhat long \&{special} strings*/ 
@d xxx3	241 /*for extremely long \&{special} strings*/ 
@d xxx4	242 /*for incredibly long \&{special} strings*/ 
@d yyy	243 /*for \&{numspecial} numbers*/ 
@d no_op	244 /*no operation*/ 

@ The last character in a \.{GF} file is followed by `|post|'; this command
introduces the postamble, which summarizes important facts that \MF\ has
accumulated. The postamble has the form
$$\vbox{\halign{\hbox{#\hfil}\cr
  |post| |p[4]| |@!ds[4]| |@!cs[4]| |@!hppp[4]| |@!vppp[4]|
   |@!min_m[4]| |@!max_m[4]| |@!min_n[4]| |@!max_n[4]|\cr
  $\langle\,$character locators$\,\rangle$\cr
  |post_post| |q[4]| |i[1]| 223's$[{\G}4]$\cr}}$$
Here |p| is a pointer to the byte following the final |eoc| in the file
(or to the byte following the preamble, if there are no characters);
it can be used to locate the beginning of \\{xxx} commands
that might have preceded the postamble. The |ds| and |cs| parameters
@^design size@> @^check sum@>
give the design size and check sum, respectively, of the font (see the
description of \.{TFM} format below).
Parameters |hppp| and |vppp| are the ratios of
pixels per point, horizontally and vertically, expressed as |scaled| integers
(i.e., multiplied by $2^{16}$); they can be used to correlate the font
with specific device resolutions, magnifications, and ``at sizes.''  Then
come |min_m|, |max_m|, |min_n|, and |max_n|, which bound the values that
registers |m| and~|n| assume in all characters in this \.{GF} file.
(These bounds need not be the best possible; |max_m| and |min_n| may, on the
other hand, be tighter than the similar bounds in |boc| commands. For
example, some character may have |min_n==-100| in its |boc|, but it might
turn out that |n| never gets lower than |-50| in any character; then
|min_n| can have any value | <= -50|. If there are no characters in the file,
it's possible to have |min_m > max_m| and/or |min_n > max_n|.)

@ Character locators are introduced by |char_loc| commands,
which specify a character residue~|c|, character escapements (|dx, dy|),
a character width~|w|, and a pointer~|p|
to the beginning of that character. (If two or more characters have the
same code~|c| modulo 256, only the last will be indicated; the others can be
located by following backpointers. Characters whose codes differ by a
multiple of 256 are assumed to share the same font metric information,
hence the \.{TFM} file contains only residues of character codes modulo~256.
This convention is intended for oriental languages, when there are many
character shapes but few distinct widths.)
@^oriental characters@>@^Chinese characters@>@^Japanese characters@>

The character escapements (|dx, dy|) are the values of \MF's \&{chardx}
and \&{chardy} parameters; they are in units of |scaled| pixels;
i.e., |dx| is in horizontal pixel units times $2^{16}$, and |dy| is in
vertical pixel units times $2^{16}$.  This is the intended amount of
displacement after typesetting the character; for \.{DVI} files, |dy|
should be zero, but other document file formats allow nonzero vertical
escapement.

The character width~|w| duplicates the information in the \.{TFM} file; it
is $2^{20}$ times the ratio of the true width to the font's design size.

The backpointer |p| points to the character's |boc|, or to the first of
a sequence of consecutive \\{xxx} or |yyy| or |no_op| commands that
immediately precede the |boc|, if such commands exist; such ``special''
commands essentially belong to the characters, while the special commands
after the final character belong to the postamble (i.e., to the font
as a whole). This convention about |p| applies also to the backpointers
in |boc| commands, even though it wasn't explained in the description
of~|boc|. @^backpointers@>

Pointer |p| might be |-1| if the character exists in the \.{TFM} file
but not in the \.{GF} file. This unusual situation can arise in \MF\ output
if the user had |proofing < 0| when the character was being shipped out,
but then made |proofing >= 0| in order to get a \.{GF} file.

@ The last part of the postamble, following the |post_post| byte that
signifies the end of the character locators, contains |q|, a pointer to the
|post| command that started the postamble.  An identification byte, |i|,
comes next; this currently equals~131, as in the preamble.

The |i| byte is followed by four or more bytes that are all equal to
the decimal number 223 (i.e., 0337 in octal). \MF\ puts out four to seven of
these trailing bytes, until the total length of the file is a multiple of
four bytes, since this works out best on machines that pack four bytes per
word; but any number of 223's is allowed, as long as there are at least four
of them. In effect, 223 is a sort of signature that is added at the very end.
@^Fuchs, David Raymond@>

This curious way to finish off a \.{GF} file makes it feasible for
\.{GF}-reading programs to find the postamble first, on most computers,
even though \MF\ wants to write the postamble last. Most operating
systems permit random access to individual words or bytes of a file, so
the \.{GF} reader can start at the end and skip backwards over the 223's
until finding the identification byte. Then it can back up four bytes, read
|q|, and move to byte |q| of the file. This byte should, of course,
contain the value 248 (|post|); now the postamble can be read, so the
\.{GF} reader can discover all the information needed for individual characters.

Unfortunately, however, standard \PASCAL\ does not include the ability to
@^system dependencies@>
access a random position in a file, or even to determine the length of a file.
Almost all systems nowadays provide the necessary capabilities, so \.{GF}
format has been designed to work most efficiently with modern operating systems.
But if \.{GF} files have to be processed under the restrictions of standard
\PASCAL, one can simply read them from front to back. This will
be adequate for most applications. However, the postamble-first approach
would facilitate a program that merges two \.{GF} files, replacing data
from one that is overridden by corresponding data in the other.

@*Extensions to the generic format.
The \\{xxx} and \\{yyy} instructions understood by \.{GFtoDVI} will be
listed now, so that we have a convenient reference to all of the special
assumptions made later.

Each special instruction begins with an \\{xxx} command, which consists of
either a keyword by itself, or a keyword followed by a space followed
by arguments. This \\{xxx} command may then be followed by \\{yyy}
commands that are understood to be arguments.

The keywords of special instructions that are intended to be used at
many different sites should be published as widely as possible in order
to minimize conflicts. The first person to establish a keyword presumably
has a right to define it; \.{GFtoDVI}, as the first program
to use extended \.{GF} commands, has the opportunity of choosing any
keywords it likes, and the responsibility of choosing reasonable ones.
Since labels are expected to account for the bulk of extended commands
in typical uses of \MF, the ``null'' keyword has been set aside to
denote a labeling command.

@ Here then are the special commands of \.{GFtoDVI}.

\def\string{$\langle\,$string$\,\rangle$}
\def\okpagebreak{\vfil\penalty-100\vfilneg}
\smallskip\hang\noindent
\.{\SP n}\string\ $x$ $y$. Here \.n denotes the type of label; the
characters \.1, \.2, \.3,~\.4 respectively denote labels forced to be
at the top, left, right, or bottom of their dot, and the characters
\.5, \.6, \.7,~\.8 stand for the same possibilities but with no dot printed.
The character \.0 instructs \.{GFtoDVI} to choose one of the first four
possibilities, if there's no overlap with other labels or dots, otherwise
an ``overflow'' entry is placed at the right of the figure. The character
\./ is the same as \.0 except that overflow entries are not produced. The
label itself is the \string\ that follows. \MF\ coordinates of the
point that is to receive this label are given by arguments $x$ and~$y$,
in units of scaled pixels. (These arguments appear in \\{yyy} commands.)
(Precise definitions of the size and positioning of labels, and of the
notion of ``conflicting'' labels, will be given later.)

\smallskip\hang\noindent
\.{rule} $x_1$ $y_1$ $x_2$ $y_2$. This command draws a line from
$(x_1,y_1)$ to $(x_2,y_2)$ in \MF\ coordinates. The present implementation
does this only if the line is either horizontal or vertical, or if its
slope matches the slope of the slant font.

\smallskip\hang\noindent
\.{title\SP}\string. This command (which is output by \MF\
when it sees a ``title statement'') specifies a string that will appear
at the top of the next proofsheet to be output by \.{GFtoDVI}.
If more than one title is given, they will appear in sequence; titles
should be short enough to fit on a single line.

\smallskip\hang\noindent
\.{titlefont\SP}\string. This command, and the other font-naming
commands below, must precede the first |boc| in the \.{GF} file.
It overrides the current font used to
typeset the titles at the top of proofsheets. \.{GFtoDVI} has default
fonts that will be used if none other are specified; the ``current'' title
font is initially the default title font.

\smallskip\hang\noindent
\.{titlefontarea\SP}\string. This command overrides the current
file area (or directory name) from which \.{GFtoDVI} will try to
find metric information for the title font.

\smallskip\hang\noindent
\.{titlefontat} $s$. This command overrides the current ``at size'' that
will be used for the title font. (See the discussion of font metric files
below, for the meaning of ``at size'' versus ``design size.'') The
value of~$s$ is given in units of scaled points.

\okpagebreak
\smallskip\hang\noindent
\.{labelfont\SP}\string. This command overrides the current font
used to typeset the labels that are superimposed on proof figures.
(The label font is fairly arbitrary, but it should be dark enough to
stand out when superimposed on gray pixels, and it should contain at
least the decimal digits and the characters `\.(', `\.)', `\.=', `\.+',
`\.-', `\.,', and `\..'.)

\smallskip\hang\noindent
\.{labelfontarea\SP}\string. This command overrides the current
file area (or directory name) from which \.{GFtoDVI} will try to
find metric information for the label font.

\smallskip\hang\noindent
\.{labelfontat} $s$. This command overrides the current ``at size'' that
will be used for the label font.

\okpagebreak
\smallskip\hang\noindent
\.{grayfont\SP}\string. This command overrides the current font
used to typeset the black pixels and the dots for labels. (Gray fonts
will be explained in detail later.)
@^gray fonts@>

\smallskip\hang\noindent
\.{grayfontarea\SP}\string. This command overrides the current
file area (or directory name) from which \.{GFtoDVI} will try to
find metric information for the gray font.

\smallskip\hang\noindent
\.{grayfontat} $s$. This command overrides the current ``at size'' that
will be used for the gray font.

\okpagebreak
\smallskip\hang\noindent
\.{slantfont\SP}\string. This command overrides the current font
used to typeset rules that are neither horizontal nor vertical. (Slant
fonts will be explained in detail later.)
@^slant fonts@>

\smallskip\hang\noindent
\.{slantfontarea\SP}\string. This command overrides the current
file area (or directory name) from which \.{GFtoDVI} will try to
find metric information for the slant font.

\smallskip\hang\noindent
\.{slantfontat} $s$. This command overrides the current ``at size'' that
will be used for the slant font.

\okpagebreak
\smallskip\hang\noindent
\.{rulethickness} $t$. This command overrides the current value used
for the thickness of rules. If the current value is negative, no rule
will be drawn; if the current value is zero, the rule thickness will
be specified by a parameter of the gray font. Each \.{rule} command
uses the rule thickness that is current at the time the command appears;
hence it is possible to get different thicknesses of rules on the same
figure. The value of $t$ is given in units of scaled points (\TeX's `\.{sp}').
At the beginning of each character the current rule thickness is zero.

\smallskip\hang\noindent
\.{offset} $x$ $y$. This command overrides the current offset values
that are added to all coordinates of a character being output; $x$ and
$y$ are given as scaled \MF\ coordinates. This simply has the effect
of repositioning the figures on the pages; the title line always appears
in the same place, but the figure can be moved up, down, left, or right.
At the beginning of each character the current offsets are zero.

\smallskip\hang\noindent
\.{xoffset} $x$. This command is output by \MF\ just before shipping out
a character whose $x$~offset is nonzero. \.{GFtoDVI} adds the specified
amount to the $x$ coordinates of all dots, labels, and rules
in the following character.

\smallskip\hang\noindent
\.{yoffset} $y$. This command is output by \MF\ just before shipping out
a character whose $y$~offset is nonzero. \.{GFtoDVI} adds the specified
amount to the $y$ coordinates of all dots, labels, and rules
in the following character.

@*Font metric data.
Before we can get into the meaty details of \.{GFtoDVI}, we need to
deal with yet another esoteric binary file format, since \.{GFtoDVI}
also does elementary typesetting operations. Therefore it has to
read important information about the fonts it will be using.
The following material (again copied almost verbatim from \TeX)
describes the contents of so-called \TeX\ font metric (\.{TFM}) files.

The idea behind \.{TFM} files is that typesetting routines
need a compact way to store the relevant information about
fonts, and computer centers need a compact way to store the
relevant information about several hundred fonts. \.{TFM} files are
compact, and most of the information they contain is highly relevant,
so they provide a solution to the problem. \.{GFtoDVI} uses only
four fonts, but interesting changes in its output will occur when
those fonts are varied.

The information in a \.{TFM} file appears in a sequence of 8-bit bytes.
Since the number of bytes is always a multiple of 4, we could
also regard the file as a sequence of 32-bit words; but \TeX\ uses the
byte interpretation, and so does \.{GFtoDVI}. The individual bytes
are considered to be unsigned numbers.

@ The first 24 bytes (6 words) of a \.{TFM} file contain twelve 16-bit
integers that give the lengths of the various subsequent portions
of the file. These twelve integers are, in order:
$$\vbox{\halign{\hfil#&$\null=\null$#\hfil\cr
|@!lf|&length of the entire file, in words;\cr
|@!lh|&length of the header data, in words;\cr
|@!bc|&smallest character code in the font;\cr
|@!ec|&largest character code in the font;\cr
|@!nw|&number of words in the width table;\cr
|@!nh|&number of words in the height table;\cr
|@!nd|&number of words in the depth table;\cr
|@!ni|&number of words in the italic correction table;\cr
|@!nl|&number of words in the lig/kern table;\cr
|@!nk|&number of words in the kern table;\cr
|@!ne|&number of words in the extensible character table;\cr
|@!np|&number of font parameter words.\cr}}$$
They are all nonnegative and less than $2^{15}$. We must have |bc-1 <= ec <= 255|,
and
$$\hbox{|lf==6+lh+(ec-bc+1)+nw+nh+nd+ni+nl+nk+ne+np|.}$$
Note that a font may contain as many as 256 characters (if |bc==0| and |ec==255|),
and as few as 0 characters (if |bc==ec+1|). When two or more 8-bit bytes are
combined to form an integer of 16 or more bits, the bytes appear in
BigEndian order.
@^BigEndian order@>

@<Glob...@>=
uint16_t @!lf, @!lh, @!bc, @!ec, @!nw, @!nh, @!nd, @!ni, @!nl, @!nk, @!ne, @!np;
   /*subfile sizes*/ 

@ The rest of the \.{TFM} file may be regarded as a sequence of ten data
arrays having the informal specification
$$\def\arr$[#1]#2${\&{array} $[#1]$ \&{of} #2}
\vbox{\halign{\hfil\\{#}&$\,:\,$\arr#\hfil\cr
header&|[0 dotdot lh-1]@t\\{stuff}@>|\cr
char\_info&|[bc dotdot ec]char_info_word|\cr
width&|[0 dotdot nw-1]fix_word|\cr
height&|[0 dotdot nh-1]fix_word|\cr
depth&|[0 dotdot nd-1]fix_word|\cr
italic&|[0 dotdot ni-1]fix_word|\cr
lig\_kern&|[0 dotdot nl-1]lig_kern_command|\cr
kern&|[0 dotdot nk-1]fix_word|\cr
exten&|[0 dotdot ne-1]extensible_recipe|\cr
param&|[1 dotdot np]fix_word|\cr}}$$
The most important data type used here is a |@!fix_word|, which is
a 32-bit representation of a binary fraction. A |fix_word| is a signed
quantity, with the two's complement of the entire word used to represent
negation. Of the 32 bits in a |fix_word|, exactly 12 are to the left of the
binary point; thus, the largest |fix_word| value is $2048-2^{-20}$, and
the smallest is $-2048$. We will see below, however, that all but two of
the |fix_word| values must lie between $-16$ and $+16$.

@ The first data array is a block of header information, which contains
general facts about the font. The header must contain at least two words,
and for \.{TFM} files to be used with Xerox printing software it must
contain at least 18 words, allocated as described below. When different
kinds of devices need to be interfaced, it may be necessary to add further
words to the header block.

\yskip\hang|header[0]| is a 32-bit check sum that \.{GFtoDVI} will copy into the
\.{DVI} output file whenever it uses the font.  Later on when the \.{DVI}
file is printed, possibly on another computer, the actual font that gets
used is supposed to have a check sum that agrees with the one in the
\.{TFM} file used by \.{GFtoDVI}. In this way, users will be warned about
potential incompatibilities. (However, if the check sum is zero in either
the font file or the \.{TFM} file, no check is made.)  The actual relation
between this check sum and the rest of the \.{TFM} file is not important;
the check sum is simply an identification number with the property that
incompatible fonts almost always have distinct check sums.
@^check sum@>

\yskip\hang|header[1]| is a |fix_word| containing the design size of the
font, in units of \TeX\ points (7227 \TeX\ points = 254 cm).  This number
must be at least 1.0; it is fairly arbitrary, but usually the design size
is 10.0 for a ``10 point'' font, i.e., a font that was designed to look
best at a 10-point size, whatever that really means. When a \TeX\ user
asks for a font `\.{at} $\delta$ \.{pt}', the effect is to override the
design size and replace it by $\delta$, and to multiply the $x$ and~$y$
coordinates of the points in the font image by a factor of $\delta$
divided by the design size.  Similarly, specific sizes can be substituted
for the design size by \.{GFtoDVI} commands like `\.{titlefontat}'.  {\sl
All other dimensions in the\/\ \.{TFM} file are |fix_word| numbers in
design-size units.} Thus, for example, the value of |param[6]|, one \.{em}
or \.{\\quad}, is often the |fix_word| value $2^{20}=1.0$, since many
fonts have a design size equal to one em.  The other dimensions must be
less than 16 design-size units in absolute value; thus, |header[1]| and
|param[1]| are the only |fix_word| entries in the whole \.{TFM} file whose
first byte might be something besides 0 or 255.  @^design size@>@^at size@>

\yskip\hang|header[2 dotdot 11]|, if present, contains 40 bytes that identify
the character coding scheme. The first byte, which must be between 0 and
39, is the number of subsequent ASCII bytes actually relevant in this
string, which is intended to specify what character-code-to-symbol
convention is present in the font.  Examples are \.{ASCII} for standard
ASCII, \.{TeX text} for fonts like \.{cmr10} and \.{cmti9}, \.{TeX math
extension} for \.{cmex10}, \.{XEROX text} for Xerox fonts, \.{GRAPHIC} for
special-purpose non-alphabetic fonts, \.{GFGRAY} for \.{GFtoDVI}'s
gray fonts, \.{GFSLANT} for \.{GFtoDVI}'s slant fonts, \.{UNSPECIFIED} for
the default case when there is no information.  Parentheses should not
appear in this name.  (Such a string is said to be in {\mc BCPL} format.)
@^coding scheme@>@^gray fonts@>@^slant fonts@>

\yskip\hang|header[12 dotdot@twhatever@>]| might also be present.

@ Next comes the |char_info| array, which contains one |char_info_word|
per character. Each |char_info_word| contains six fields packed into
four bytes as follows.

\yskip\hang first byte: |@!width_index| (8 bits)\par
\hang second byte: |@!height_index| (4 bits) times 16, plus |@!depth_index|
  (4~bits)\par
\hang third byte: |@!italic_index| (6 bits) times 4, plus |@!tag|
  (2~bits)\par
\hang fourth byte: |@!rem| (8 bits)\par
\yskip\noindent
The actual width of a character is \\{width}|[width_index]|, in design-size
units; this is a device for compressing information, since many characters
have the same width. Since it is quite common for many characters
to have the same height, depth, or italic correction, the \.{TFM} format
imposes a limit of 16 different heights, 16 different depths, and
64 different italic corrections.

Incidentally, the relation $\\{width}[0]=\\{height}[0]=\\{depth}[0]=
\\{italic}[0]=0$ should always hold, so that an index of zero implies a
value of zero.  The |width_index| should never be zero unless the
character does not exist in the font, since a character is valid if and
only if it lies between |bc| and |ec| and has a nonzero |width_index|.

@ The |tag| field in a |char_info_word| has four values that explain how to
interpret the |rem| field.

\yskip\hang|tag==0| (|no_tag|) means that |rem| is unused.\par
\hang|tag==1| (|lig_tag|) means that this character has a ligature/kerning
program starting at |lig_kern[rem]|.\par
\hang|tag==2| (|list_tag|) means that this character is part of a chain of
characters of ascending sizes, and not the largest in the chain.  The
|rem| field gives the character code of the next larger character.\par
\hang|tag==3| (|ext_tag|) means that this character code represents an
extensible character, i.e., a character that is built up of smaller pieces
so that it can be made arbitrarily large. The pieces are specified in
|@!exten[rem]|.\par

@d no_tag	0 /*vanilla character*/ 
@d lig_tag	1 /*character has a ligature/kerning program*/ 
@d list_tag	2 /*character has a successor in a charlist*/ 
@d ext_tag	3 /*character is extensible*/ 

@ The |lig_kern| array contains instructions in a simple programming language
that explains what to do for special letter pairs. Each word in this array is a
|@!lig_kern_command| of four bytes.

\yskip\hang first byte: |skip_byte|, indicates that this is the final program
  step if the byte is 128 or more, otherwise the next step is obtained by
  skipping this number of intervening steps.\par
\hang second byte: |next_char|, ``if |next_char| follows the current character,
  then perform the operation and stop, otherwise continue.''\par
\hang third byte: |op_byte|, indicates a ligature step if less than~128,
  a kern step otherwise.\par
\hang fourth byte: |rem|.\par
\yskip\noindent
In a kern step, an
additional space equal to |kern[256*(op_byte-128)+rem]| is inserted
between the current character and |next_char|. This amount is
often negative, so that the characters are brought closer together
by kerning; but it might be positive.

There are eight kinds of ligature steps, having |op_byte| codes $4a+2b+c$ where
$0\le a\le b+c$ and $0\le b,c\le1$. The character whose code is
|rem| is inserted between the current character and |next_char|;
then the current character is deleted if $b=0$, and |next_char| is
deleted if $c=0$; then we pass over $a$~characters to reach the next
current character (which may have a ligature/kerning program of its own).

If the very first instruction of the |lig_kern| array has |skip_byte==255|,
the |next_char| byte is the so-called right boundary character of this font;
the value of |next_char| need not lie between |bc| and~|ec|.
If the very last instruction of the |lig_kern| array has |skip_byte==255|,
there is a special ligature/kerning program for a left boundary character,
beginning at location |256*op_byte+rem|.
The interpretation is that \TeX\ puts implicit boundary characters
before and after each consecutive string of characters from the same font.
These implicit characters do not appear in the output, but they can affect
ligatures and kerning.

If the very first instruction of a character's |lig_kern| program has
|skip_byte > 128|, the program actually begins in location
|256*op_byte+rem|. This feature allows access to large |lig_kern|
arrays, because the first instruction must otherwise
appear in a location | <= 255|.

Any instruction with |skip_byte > 128| in the |lig_kern| array must have
|256*op_byte+rem < nl|. If such an instruction is encountered during
normal program execution, it denotes an unconditional halt; no ligature
or kerning command is performed.

@d stop_flag	128 /*value indicating `\.{STOP}' in a lig/kern program*/ 
@d kern_flag	128 /*op code for a kern step*/ 

@ Extensible characters are specified by an |@!extensible_recipe|, which
consists of four bytes called |@!top|, |@!mid|, |@!bot|, and |@!rep| (in this
order). These bytes are the character codes of individual pieces used to
build up a large symbol.  If |top|, |mid|, or |bot| are zero, they are not
present in the built-up result. For example, an extensible vertical line is
like an extensible bracket, except that the top and bottom pieces are missing.

@ The final portion of a \.{TFM} file is the |param| array, which is another
sequence of |fix_word| values.

\yskip\hang|param[1]==@!slant| is the amount of italic slant.
For example, |slant==.25| means that when you go
up one unit, you also go .25 units to the right. The |slant| is a pure
number; it's the only |fix_word| other than the design size itself that is
not scaled by the design size.

\hang|param[2]==space| is the normal spacing between words in text.
Note that character |' '| in the font need not have anything to do with
blank spaces.

\hang|param[3]==space_stretch| is the amount of glue stretching between words.

\hang|param[4]==space_shrink| is the amount of glue shrinking between words.

\hang|param[5]==x_height| is the height of letters for which accents don't
have to be raised or lowered.

\hang|param[6]==quad| is the size of one em in the font.

\hang|param[7]==extra_space| is the amount added to |param[2]| at the
ends of sentences.

When the character coding scheme is \.{GFGRAY} or \.{GFSLANT}, the font is
supposed to contain an additional parameter called
|default_rule_thickness|. Other special parameters go with other coding
schemes.

@*Input from binary files.
We have seen that \.{GF} and \.{DVI} and \.{TFM} files are sequences of
8-bit bytes.  The bytes appear physically in what is called a `|
File 0 dotdot 255|' in \PASCAL\ lingo.

Packing is system dependent, and many \PASCAL\ systems fail to implement
such files in a sensible way (at least, from the viewpoint of producing
good production software).  For example, some systems treat all
byte-oriented files as text, looking for end-of-line marks and such
things. Therefore some system-dependent code is often needed to deal with
binary files, even though most of the program in this section of
\.{GFtoDVI} is written in standard \PASCAL.
@^system dependencies@>

One common way to solve the problem is to consider files of |int|
numbers, and to convert an integer in the range $-2^{31}\L x<2^{31}$ to
a sequence of four bytes $(a,b,c,d)$ using the following code, which
avoids the controversial integer division of negative numbers:
$$\vbox{\halign{#\hfil\cr
|if (x >= 0) a=x/0100000000|\cr
|else{@+x=(x+010000000000)+010000000000;a=x/0100000000+128;|\cr
\quad|} |;\cr
|x=x%0100000000;|\cr
|b=x/0200000;x=x%0200000;|\cr
|c=x/0400;d=x%0400;|\cr}}$$
The four bytes are then kept in a buffer and output one by one. (On 36-bit
computers, an additional division by 16 is necessary at the beginning.
Another way to separate an integer into four bytes is to use/abuse
\PASCAL's variant records, storing an integer and retrieving bytes that are
packed in the same place; {\sl caveat implementor!\/}) It is also desirable
in some cases to read a hundred or so integers at a time, maintaining a
larger buffer.

We shall stick to simple \PASCAL\ in this program, for reasons of clarity,
even if such simplicity is sometimes unrealistic.

@<Types ...@>=
typedef uint8_t eight_bits; /*unsigned one-byte quantity*/ 
typedef struct {@+FILE *f;@+eight_bits@,d;@+} byte_file; /*files that contain binary data*/ 

@ The program deals with three binary file variables: |gf_file| is the main
input file that we are converting into a document; |dvi_file| is the main
output file that will specify that document; and |tfm_file| is
the current font metric file from which character-width information is
being read.

@<Glob...@>=
byte_file @!gf_file; /*the character data we are reading*/ 
byte_file @!dvi_file; /*the typesetting instructions we are writing*/ 
byte_file @!tfm_file; /*a font metric file*/ 

@ To prepare these files for input or output, we |reset| or |rewrite|
them. An extension of \PASCAL\ is needed, since we want to associate
it with external files whose names are specified dynamically (i.e., not
known at compile time). The following code assumes that `|reset(f, s)|' and
`|rewrite(f, s)|' do this, when |f| is a file variable and |s| is a string
variable that specifies the file name.
@^system dependencies@>

@p void open_gf_file(void) /*prepares to read packed bytes in |gf_file|*/ 
{@+reset(gf_file, name_of_file);
cur_loc=0;
} 
@#
void open_tfm_file(void) /*prepares to read packed bytes in |tfm_file|*/ 
{@+reset(tfm_file, name_of_file);
} 
@#
void open_dvi_file(void) /*prepares to write packed bytes in |dvi_file|*/ 
{@+rewrite(dvi_file, name_of_file);
} 

@ If you looked carefully at the preceding code, you probably asked,
``What are |cur_loc| and |name_of_file|?'' Good question. They are global
variables: The integer |cur_loc| tells which byte of the input file will
be read next, and the string |name_of_file| will be set to the current
file name before the file-opening procedures are called.

@<Glob...@>=
int @!cur_loc; /*current byte number in |gf_file|*/ 
uint8_t @!name_of_file0[file_name_size+1], *const @!name_of_file = @!name_of_file0-1; /*external file name*/

@ It turns out to be convenient to read four bytes at a time, when we are
inputting from \.{TFM} files. The input goes into global variables
|b0|, |b1|, |b2|, and |b3|, with |b0| getting the first byte and |b3|
the fourth.

@<Glob...@>=
eight_bits @!b0, @!b1, @!b2, @!b3; /*four bytes input at once*/ 

@ The |read_tfm_word| procedure sets |b0| through |b3| to the next
four bytes in the current \.{TFM} file.
@^system dependencies@>

@p void read_tfm_word(void)
{@+read(tfm_file, b0);read(tfm_file, b1);
read(tfm_file, b2);read(tfm_file, b3);
} 

@ We shall use another set of simple functions to read the next byte or
bytes from |gf_file|. There are four possibilities, each of which is
treated as a separate function in order to minimize the overhead for
subroutine calls.
@^system dependencies@>

@p int get_byte(void) /*returns the next byte, unsigned*/ 
{@+eight_bits b;
if (eof(gf_file)) return 0;
else{@+read(gf_file, b);incr(cur_loc);return b;
  } 
} 
@#
int get_two_bytes(void) /*returns the next two bytes, unsigned*/ 
{@+eight_bits a, @!b;
read(gf_file, a);read(gf_file, b);
cur_loc=cur_loc+2;
return a*256+b;
} 
@#
int get_three_bytes(void) /*returns the next three bytes, unsigned*/ 
{@+eight_bits a, @!b, @!c;
read(gf_file, a);read(gf_file, b);read(gf_file, c);
cur_loc=cur_loc+3;
return(a*256+b)*256+c;
} 
@#
int signed_quad(void) /*returns the next four bytes, signed*/ 
{@+eight_bits a, @!b, @!c, @!d;
read(gf_file, a);read(gf_file, b);read(gf_file, c);read(gf_file, d);
cur_loc=cur_loc+4;
if (a < 128) return((a*256+b)*256+c)*256+d;
else return(((a-256)*256+b)*256+c)*256+d;
} 

@*Reading the font information.
Now let's get down to brass tacks and consider the more substantial
routines that actually convert \.{TFM} data into a form suitable for
computation.  The routines in this part of the program have been borrowed
from \TeX, with slight changes, since \.{GFtoDVI} has to do some of the
things that \TeX\ does.

The \.{TFM} data is stored in a large array called
|font_info|. Each item of |font_info| is a |memory_word|; the |fix_word|
data gets converted into |scaled| entries, while everything else goes into
words of type |four_quarters|. (These data structures are special cases of
the more general memory words of \TeX. On some machines it is necessary to
define |min_quarterword==-128| and |max_quarterword==127| in order to pack
four quarterwords into a single word.)
@^system dependencies@>

@d min_quarterword	0 /*change this to allow efficient packing, if necessary*/ 
@d max_quarterword	255 /*ditto*/ 
@d qi(X)	X+min_quarterword
   /*to put an |eight_bits| item into a quarterword*/ 
@d qo(X)	X-min_quarterword
   /*to take an |eight_bits| item out of a quarterword*/ 
@d title_font	1
@d label_font	2
@d gray_font	3
@d slant_font	4
@d logo_font	5
@d non_char	qi(256)
@d non_address	font_mem_size

@<Types ...@>=
typedef uint16_t font_index;
typedef uint8_t quarterword; /*1/4 of a word*/ 
typedef struct { @;@/
  quarterword @!b0;
  quarterword @!b1;
  quarterword @!b2;
  quarterword @!b3;
  } four_quarters;
typedef uint8_t two_choices;
typedef struct { @;@/
  union { 
  scaled @!sc;
  four_quarters @!qqqq;
  };} memory_word;
typedef uint8_t internal_font_number;

@ Besides |font_info|, there are also a number of index arrays that point
into it, so that we can locate width and height information, etc.  For
example, the |char_info| data for character |c| in font |f| will be in
|font_info[char_base[f]+c].qqqq|; and if |w| is the |width_index| part of
this word (the |b0| field), the width of the character is
|font_info[width_base[f]+w].sc|. (These formulas assume that
|min_quarterword| has already been added to |w|, but not to |c|.)

@<Glob...@>=
memory_word @!font_info[font_mem_size+1]; /*the font metric data*/ 
font_index @!fmem_ptr; /*first unused word of |font_info|*/ 
four_quarters @!font_check0[logo_font-title_font+1], *const @!font_check = @!font_check0-title_font; /*check sum*/ 
scaled @!font_size0[logo_font-title_font+1], *const @!font_size = @!font_size0-title_font; /*``at'' size*/ 
scaled @!font_dsize0[logo_font-title_font+1], *const @!font_dsize = @!font_dsize0-title_font; /*``design'' size*/ 
eight_bits @!font_bc0[logo_font-title_font+1], *const @!font_bc = @!font_bc0-title_font;
   /*beginning (smallest) character code*/ 
eight_bits @!font_ec0[logo_font-title_font+1], *const @!font_ec = @!font_ec0-title_font;
   /*ending (largest) character code*/ 
int @!char_base0[logo_font-title_font+1], *const @!char_base = @!char_base0-title_font;
   /*base addresses for |char_info|*/ 
int @!width_base0[logo_font-title_font+1], *const @!width_base = @!width_base0-title_font;
   /*base addresses for widths*/ 
int @!height_base0[logo_font-title_font+1], *const @!height_base = @!height_base0-title_font;
   /*base addresses for heights*/ 
int @!depth_base0[logo_font-title_font+1], *const @!depth_base = @!depth_base0-title_font;
   /*base addresses for depths*/ 
int @!italic_base0[logo_font-title_font+1], *const @!italic_base = @!italic_base0-title_font;
   /*base addresses for italic corrections*/ 
int @!lig_kern_base0[logo_font-title_font+1], *const @!lig_kern_base = @!lig_kern_base0-title_font;
   /*base addresses for ligature/kerning programs*/ 
int @!kern_base0[logo_font-title_font+1], *const @!kern_base = @!kern_base0-title_font;
   /*base addresses for kerns*/ 
int @!exten_base0[logo_font-title_font+1], *const @!exten_base = @!exten_base0-title_font;
   /*base addresses for extensible recipes*/ 
int @!param_base0[logo_font-title_font+1], *const @!param_base = @!param_base0-title_font;
   /*base addresses for font parameters*/ 
font_index @!bchar_label0[logo_font-title_font+1], *const @!bchar_label = @!bchar_label0-title_font;
   /*start of |lig_kern| program for left boundary character,
  |non_address| if there is none*/ 
uint16_t @!font_bchar0[logo_font-title_font+1], *const @!font_bchar = @!font_bchar0-title_font;
   /*right boundary character, |non_char| if there is none*/ 

@ @<Set init...@>=
fmem_ptr=0;

@ Of course we want to define macros that suppress the detail of how font
information is actually packed, so that we don't have to write things like
$$\hbox{|font_info[width_base[f]+font_info[char_base[f]+c].qqqq.b0].sc|}$$
too often. The \.{WEB} definitions here make |char_info(f)(c)| the
|four_quarters| word of font information corresponding to character
|c| of font |f|. If |q| is such a word, |char_width(f)(q)| will be
the character's width; hence the long formula above is at least
abbreviated to
$$\hbox{|char_width(f)(char_info(f)(c))|.}$$
In practice we will try to fetch |q| first and look at several of its
fields at the same time.

The italic correction of a character will be denoted by
|char_italic(f)(q)|, so it is analogous to |char_width|.  But we will get
at the height and depth in a slightly different way, since we usually want
to compute both height and depth if we want either one.  The value of
|height_depth(q)| will be the 8-bit quantity
$$b=|height_index|\times16+|depth_index|,$$ and if |b| is such a byte we
will write |char_height(f)(b)| and |char_depth(f)(b)| for the height and
depth of the character |c| for which |q==char_info(f)(c)|. Got that?

The tag field will be called |char_tag(q)|; and the remainder byte will be
called |rem_byte(q)|.

@d char_info_end(X)	X].qqqq
@d char_info(X)	font_info[char_base[X]+char_info_end
@d char_width_end(X)	X.b0].sc
@d char_width(X)	font_info[width_base[X]+char_width_end
@d char_exists(X)	(X.b0 > min_quarterword)
@d char_italic_end(X)	(qo(X.b2))/4].sc
@d char_italic(X)	font_info[italic_base[X]+char_italic_end
@d height_depth(X)	qo(X.b1)
@d char_height_end(X)	(X)/16].sc
@d char_height(X)	font_info[height_base[X]+char_height_end
@d char_depth_end(X)	X%16].sc
@d char_depth(X)	font_info[depth_base[X]+char_depth_end
@d char_tag(X)	((qo(X.b2))%4)
@d skip_byte(X)	qo(X.b0)
@d next_char(X)	X.b1
@d op_byte(X)	qo(X.b2)
@d rem_byte(X)	X.b3

@ Here are some macros that help process ligatures and kerns.
We write |char_kern(f)(j)| to find the amount of kerning specified by
kerning command~|j| in font~|f|.

@d lig_kern_start(X)	lig_kern_base[X]+rem_byte /*beginning of lig/kern program*/ 
@d lig_kern_restart_end(X)	256*(op_byte(X))+rem_byte(X)
@d lig_kern_restart(X)	lig_kern_base[X]+lig_kern_restart_end
@d char_kern_end(X)	256*(op_byte(X)-128)+rem_byte(X)].sc
@d char_kern(X)	font_info[kern_base[X]+char_kern_end

@ Font parameters are referred to as |slant(f)|, |space(f)|, etc.

@d param_end(X)	param_base[X]].sc
@d param(X)	font_info[X+param_end
@d slant	param(1) /*slant to the right, per unit distance upward*/ 
@d space	param(2) /*normal space between words*/ 
@d x_height	param(5) /*one ex*/ 
@d default_rule_thickness	param(8) /*thickness of rules*/ 

@ Here is the subroutine that inputs the information on |tfm_file|, assuming
that the file has just been reset. Parameter~|f| tells which metric file is
being read (either |title_font| or |label_font| or |gray_font| or |slant_font|
or |logo_font|); parameter~|s| is the ``at'' size, which will be
substituted for the design size if it is positive.

This routine does only limited checking of the validity of the file,
because another program (\.{TFtoPL}) is available to diagnose errors in
the rare case that something is amiss.

@d abend	goto bad_tfm /*do this when the \.{TFM} data is wrong*/ 

@p void read_font_info(int @!f, scaled @!s) /*input a \.{TFM} file*/ 
{@+
font_index k; /*index into |font_info|*/ 
uint16_t @!lf, @!lh, @!bc, @!ec, @!nw, @!nh, @!nd, @!ni, @!nl, @!nk, @!ne, @!np;
   /*sizes of subfiles*/ 
int @!bch_label; /*left boundary label for ligatures*/ 
uint16_t @!bchar; /*right boundary character for ligatures*/ 
four_quarters @!qw;scaled @!sw; /*accumulators*/ 
scaled @!z; /*the design size or the ``at'' size*/ 
int @!alpha;uint8_t @!beta;
   /*auxiliary quantities used in fixed-point multiplication*/ 
@<Read and check the font data; |abend| if the \.{TFM} file is malformed; otherwise
|goto done|@>;
bad_tfm: print_nl("Bad TFM file for");
@.Bad TFM file...@>
switch (f) {
case title_font: abort("titles!")@;@+break;
case label_font: abort("labels!")@;@+break;
case gray_font: abort("pixels!")@;@+break;
case slant_font: abort("slants!")@;@+break;
case logo_font: abort("METAFONT logo!");
}  /*there are no other cases*/ 
done: ; /*it might be good to close |tfm_file| now*/ 
} 

@ @<Read and check...@>=
@<Read the {\.{TFM}} size fields@>;
@<Use size fields to allocate font information@>;
@<Read the {\.{TFM}} header@>;
@<Read character data@>;
@<Read box dimensions@>;
@<Read ligature/kern program@>;
@<Read extensible character recipes@>;
@<Read font parameters@>;
@<Make final adjustments and |goto done|@>@;

@ @d read_two_halves_end(X)	X=b2*256+b3
@d read_two_halves(X)	read_tfm_word();X=b0*256+b1;read_two_halves_end

@<Read the {\.{TFM}} size fields@>=
{@+read_two_halves(lf)(lh);
read_two_halves(bc)(ec);
if ((bc > ec+1)||(ec > 255)) abend;
if (bc > 255)  /*|bc==256| and |ec==255|*/ 
  {@+bc=1;ec=0;
  } 
read_two_halves(nw)(nh);
read_two_halves(nd)(ni);
read_two_halves(nl)(nk);
read_two_halves(ne)(np);
if (lf!=6+lh+(ec-bc+1)+nw+nh+nd+ni+nl+nk+ne+np) abend;
} 

@ The preliminary settings of the index variables |width_base|,
|lig_kern_base|, |kern_base|, and |exten_base| will be corrected later by
subtracting |min_quarterword| from them; and we will subtract 1 from
|param_base| too. It's best to forget about such anomalies until later.

@<Use size fields to allocate font information@>=
lf=lf-6-lh; /*|lf| words should be loaded into |font_info|*/ 
if (np < 8) lf=lf+8-np; /*at least eight parameters will appear*/ 
if (fmem_ptr+lf > font_mem_size) abort("No room for TFM file!");
@.No room for TFM file@>
char_base[f]=fmem_ptr-bc;
width_base[f]=char_base[f]+ec+1;
height_base[f]=width_base[f]+nw;
depth_base[f]=height_base[f]+nh;
italic_base[f]=depth_base[f]+nd;
lig_kern_base[f]=italic_base[f]+ni;
kern_base[f]=lig_kern_base[f]+nl;
exten_base[f]=kern_base[f]+nk;
param_base[f]=exten_base[f]+ne

@ Only the first two words of the header are needed by \.{GFtoDVI}.

@d store_four_quarters(X)	
  {@+read_tfm_word();
  qw.b0=qi(b0);qw.b1=qi(b1);qw.b2=qi(b2);qw.b3=qi(b3);
  X=qw;
  } 

@<Read the {\.{TFM}} header@>=
{@+if (lh < 2) abend;
store_four_quarters(font_check[f]);
read_tfm_word();
if (b0 > 127) abend; /*design size must be positive*/ 
z=((b0*256+b1)*256+b2)*16+(b3/16);
if (z < unity) abend;
while (lh > 2) 
  {@+read_tfm_word();decr(lh); /*ignore the rest of the header*/ 
  } 
font_dsize[f]=z;
if (s > 0) z=s;
font_size[f]=z;
} 

@ @<Read character data@>=
for (k=fmem_ptr; k<=width_base[f]-1; k++) 
  {@+store_four_quarters(font_info[k].qqqq);
  if ((b0 >= nw)||(b1/020 >= nh)||(b1%020 >= nd)||
    (b2/4 >= ni)) abend;
  switch (b2%4) {
  case lig_tag: if (b3 >= nl) abend;@+break;
  case ext_tag: if (b3 >= ne) abend;@+break;
  case no_tag: case list_tag: do_nothing;
  }  /*there are no other cases*/ 
  } 

@ A |fix_word| whose four bytes are $(b0,b1,b2,b3)$ from left to right
represents the number
$$x=\left\{\vcenter{\halign{$#$,\hfil\qquad&if $#$\hfil\cr
b_1\cdot2^{-4}+b_2\cdot2^{-12}+b_3\cdot2^{-20}&b_0=0;\cr
-16+b_1\cdot2^{-4}+b_2\cdot2^{-12}+b_3\cdot2^{-20}&b_0=255.\cr}}\right.$$
(No other choices of |b0| are allowed, since the magnitude of a number in
design-size units must be less than 16.)  We want to multiply this
quantity by the integer~|z|, which is known to be less than $2^{27}$. Let
$\alpha=16z$.  If $|z|<2^{23}$, the individual multiplications $b\cdot z$,
$c\cdot z$, $d\cdot z$ cannot overflow; otherwise we will divide |z| by 2,
4, 8, or 16, to obtain a multiplier less than $2^{23}$, and we can
compensate for this later. If |z| has thereby been replaced by
$|z|^\prime=|z|/2^e$, let $\beta=2^{4-e}$; we shall compute
$$\lfloor(b_1+b_2\cdot2^{-8}+b_3\cdot2^{-16})\,z^\prime/\beta\rfloor$$
if $a=0$, or the same quantity minus $\alpha$ if $a=255$.

@d store_scaled(X)	{@+read_tfm_word();
  sw=(((((b3*z)/0400)+(b2*z))/0400)+(b1*z))/beta;
  if (b0==0) X=sw;@+else if (b0==255) X=sw-alpha;@+else abend;
  } 

@<Read box dimensions@>=
{@+@<Replace |z| by $|z|^\prime$ and compute $\alpha,\beta$@>;
for (k=width_base[f]; k<=lig_kern_base[f]-1; k++) 
  store_scaled(font_info[k].sc);
if (font_info[width_base[f]].sc!=0) abend; /*\\{width}[0] must be zero*/ 
if (font_info[height_base[f]].sc!=0) abend; /*\\{height}[0] must be zero*/ 
if (font_info[depth_base[f]].sc!=0) abend; /*\\{depth}[0] must be zero*/ 
if (font_info[italic_base[f]].sc!=0) abend; /*\\{italic}[0] must be zero*/ 
} 

@ @<Replace |z|...@>=
{@+alpha=16*z;beta=16;
while (z >= 040000000) 
  {@+z=z/2;beta=beta/2;
  } 
} 

@ @d check_byte_range(X)	{@+if ((X < bc)||(X > ec)) abend;@+} 

@<Read ligature/kern program@>=
{@+bch_label=077777;bchar=256;
if (nl > 0) 
  {@+for (k=lig_kern_base[f]; k<=kern_base[f]-1; k++) 
    {@+store_four_quarters(font_info[k].qqqq);
    if (b0 > stop_flag) 
      {@+if (256*b2+b3 >= nl) abend;
      if (b0==255) if (k==lig_kern_base[f]) bchar=b1;
      } 
    else{@+if (b1!=bchar) check_byte_range(b1);
      if (b2 < kern_flag) check_byte_range(b3)@;
      else if (256*(b2-128)+b3 >= nk) abend;
      } 
    } 
  if (b0==255) bch_label=256*b2+b3;
  } 
for (k=kern_base[f]; k<=exten_base[f]-1; k++) 
  store_scaled(font_info[k].sc);
} 

@ @<Read extensible character recipes@>=
for (k=exten_base[f]; k<=param_base[f]-1; k++) 
  {@+store_four_quarters(font_info[k].qqqq);
  if (b0!=0) check_byte_range(b0);
  if (b1!=0) check_byte_range(b1);
  if (b2!=0) check_byte_range(b2);
  check_byte_range(b3);
  } 

@ @<Read font parameters@>=
{@+for (k=1; k<=np; k++) 
  if (k==1)  /*the |slant| parameter is a pure number*/ 
    {@+read_tfm_word();
    if (b0 > 127) sw=b0-256;@+else sw=b0;
    sw=sw*0400+b1;sw=sw*0400+b2;
    font_info[param_base[f]].sc=(sw*020)+(b3/020);
    } 
  else store_scaled(font_info[param_base[f]+k-1].sc);
for (k=np+1; k<=8; k++) font_info[param_base[f]+k-1].sc=0;
} 

@ Now to wrap it up, we have checked all the necessary things about the \.{TFM}
file, and all we need to do is put the finishing touches on the data for
the new font.

@d adjust(X)	X[f]=qo(X[f])
   /*correct for the excess |min_quarterword| that was added*/ 

@<Make final adjustments...@>=
font_bc[f]=bc;font_ec[f]=ec;
if (bch_label < nl) bchar_label[f]=bch_label+lig_kern_base[f];
else bchar_label[f]=non_address;
font_bchar[f]=qi(bchar);
adjust(width_base);adjust(lig_kern_base);
adjust(kern_base);adjust(exten_base);
decr(param_base[f]);
fmem_ptr=fmem_ptr+lf;goto done

@*The string pool.
\.{GFtoDVI} remembers strings by putting them into an array called
|str_pool|. The |str_start| array tells where each string starts in the pool.

@<Types ...@>=
typedef uint16_t pool_pointer; /*for variables that point into |str_pool|*/ 
typedef uint16_t str_number; /*for variables that point into |str_start|*/ 

@ As new strings enter, we keep track of the storage currently used, by
means of two global variables called |pool_ptr| and |str_ptr|. These are
periodically reset to their initial values when we move from one character
to another, because most strings are of only temporary interest.

@<Glob...@>=
ASCII_code @!str_pool[pool_size+1]; /*the characters*/ 
pool_pointer @!str_start[max_strings+1]; /*the starting pointers*/ 
pool_pointer @!pool_ptr; /*first unused position in |str_pool|*/ 
str_number @!str_ptr; /*start of the current string being created*/ 
str_number @!init_str_ptr; /*|str_ptr| setting when a new character starts*/ 

@ Several of the elementary string operations are performed using \.{WEB}
macros instead of using \PASCAL\ procedures, because many of the
operations are done quite frequently and we want to avoid the
overhead of procedure calls. For example, here is
a simple macro that computes the length of a string.
@.WEB@>

@d length(X)	(str_start[X+1]-str_start[X]) /*the number of characters
  in string number \#*/ 

@ Strings are created by appending character codes to |str_pool|.
The macro called |append_char|, defined here, does not check to see if the
value of |pool_ptr| has gotten too high; that test is supposed to be
made before |append_char| is used.

To test if there is room to append |l| more characters to |str_pool|,
we shall write |str_room(l)|, which aborts \.{GFtoDVI} and gives an
apologetic error message if there isn't enough room.

@d append_char(X)	 /*put |ASCII_code| \# at the end of |str_pool|*/ 
{@+str_pool[pool_ptr]=X;incr(pool_ptr);
} 
@d str_room(X)	 /*make sure that the pool hasn't overflowed*/ 
  {@+if (pool_ptr+X > pool_size) 
    abort("Too many strings!");
@.Too many strings@>
  } 

@ Once a sequence of characters has been appended to |str_pool|, it
officially becomes a string when the function |make_string| is called.
This function returns the identification number of the new string as its
value.

@p str_number make_string(void) /*current string enters the pool*/ 
{@+if (str_ptr==max_strings) 
  abort("Too many labels!");
@.Too many labels@>
incr(str_ptr);str_start[str_ptr]=pool_ptr;
return str_ptr-1;
} 

@ The first strings in the string pool are the keywords that \.{GFtoDVI}
recognizes in the \\{xxx} commands of a \.{GF} file. They are entered
into |str_pool| by means of a tedious bunch of assignment statements,
together with calls on the |first_string| subroutine.

@d init_str0(X)	first_string(X)
@d init_str1(X)	buffer[1]=X;init_str0
@d init_str2(X)	buffer[2]=X;init_str1
@d init_str3(X)	buffer[3]=X;init_str2
@d init_str4(X)	buffer[4]=X;init_str3
@d init_str5(X)	buffer[5]=X;init_str4
@d init_str6(X)	buffer[6]=X;init_str5
@d init_str7(X)	buffer[7]=X;init_str6
@d init_str8(X)	buffer[8]=X;init_str7
@d init_str9(X)	buffer[9]=X;init_str8
@d init_str10(X)	buffer[10]=X;init_str9
@d init_str11(X)	buffer[11]=X;init_str10
@d init_str12(X)	buffer[12]=X;init_str11
@d init_str13(X)	buffer[13]=X;init_str12
@d longest_keyword	13

@p void first_string(int @!c)
{@+if (str_ptr!=c) abort("?"); /*internal consistency check*/
@.?@>
while (l > 0) 
  {@+append_char(buffer[l]);decr(l);
  } 
incr(str_ptr);str_start[str_ptr]=pool_ptr;
} 

@ @<Glob...@>=
int @!l; /*length of string being made by |first_string|*/ 

@ Here are the tedious assignments just promised.
String number 0 is the empty string.

@d null_string	0 /*the empty keyword*/ 
@d area_code	4 /*add to font code for the `\.{area}' keywords*/ 
@d at_code	8 /*add to font code for the `\.{at}' keywords*/ 
@d rule_code	13 /*code for the keyword `\.{rule}'*/ 
@d title_code	14 /*code for the keyword `\.{title}'*/ 
@d rule_thickness_code	15 /*code for the keyword `\.{rulethickness}'*/ 
@d offset_code	16 /*code for the keyword `\.{offset}'*/ 
@d x_offset_code	17 /*code for the keyword `\.{xoffset}'*/ 
@d y_offset_code	18 /*code for the keyword `\.{yoffset}'*/ 
@d max_keyword	18 /*largest keyword code number*/ 

@<Initialize the strings@>=
str_ptr=0;pool_ptr=0;str_start[0]=0;@/
l=0;init_str0(null_string);@/
l=9;init_str9('t')('i')('t')('l')('e')('f')('o')('n')('t')(title_font);@/
l=9;init_str9('l')('a')('b')('e')('l')('f')('o')('n')('t')(label_font);@/
l=8;init_str8('g')('r')('a')('y')('f')('o')('n')('t')(gray_font);@/
l=9;init_str9('s')('l')('a')('n')('t')('f')('o')('n')('t')(slant_font);@/
l=13;init_str13('t')('i')('t')('l')('e')
  ('f')('o')('n')('t')('a')('r')('e')('a')(title_font+area_code);@/
l=13;init_str13('l')('a')('b')('e')('l')
  ('f')('o')('n')('t')('a')('r')('e')('a')(label_font+area_code);@/
l=12;init_str12('g')('r')('a')('y')
  ('f')('o')('n')('t')('a')('r')('e')('a')(gray_font+area_code);@/
l=13;init_str13('s')('l')('a')('n')('t')
  ('f')('o')('n')('t')('a')('r')('e')('a')(slant_font+area_code);@/
l=11;init_str11('t')('i')('t')('l')('e')
  ('f')('o')('n')('t')('a')('t')(title_font+at_code);@/
l=11;init_str11('l')('a')('b')('e')('l')
  ('f')('o')('n')('t')('a')('t')(label_font+at_code);@/
l=10;init_str10('g')('r')('a')('y')
  ('f')('o')('n')('t')('a')('t')(gray_font+at_code);@/
l=11;init_str11('s')('l')('a')('n')('t')
  ('f')('o')('n')('t')('a')('t')(slant_font+at_code);@/
l=4;init_str4('r')('u')('l')('e')(rule_code);@/
l=5;init_str5('t')('i')('t')('l')('e')(title_code);@/
l=13;init_str13('r')('u')('l')('e')
  ('t')('h')('i')('c')('k')('n')('e')('s')('s')(rule_thickness_code);@/
l=6;init_str6('o')('f')('f')('s')('e')('t')(offset_code);@/
l=7;init_str7('x')('o')('f')('f')('s')('e')('t')(x_offset_code);@/
l=7;init_str7('y')('o')('f')('f')('s')('e')('t')(y_offset_code);@/

@ We will also find it useful to have the following strings. (The names of
default fonts will presumably be different at different sites.)
@^system dependencies@>
@^default fonts@>

@d gf_ext	(max_keyword+1) /*string number for `\.{.gf}'*/ 
@d dvi_ext	(max_keyword+2) /*string number for `\.{.dvi}'*/ 
@d tfm_ext	(max_keyword+3) /*string number for `\.{.tfm}'*/ 
@d page_header	(max_keyword+4) /*string number for `\.{\ \ Page\ }'*/ 
@d char_header	(max_keyword+5) /*string number for `\.{\ \ Character\ }'*/ 
@d ext_header	(max_keyword+6) /*string number for `\.{\ \ Ext\ }'*/ 
@d left_quotes	(max_keyword+7) /*string number for `\.{\ \ ``}'*/ 
@d right_quotes	(max_keyword+8) /*string number for `\.{''}'*/ 
@d equals_sign	(max_keyword+9) /*string number for `\.{ = }'*/ 
@d plus_sign	(max_keyword+10) /*string number for `\.{ + (}'*/ 
@d default_title_font	(max_keyword+11)
   /*string number for the default |title_font|*/ 
@d default_label_font	(max_keyword+12)
   /*string number for the default |label_font|*/ 
@d default_gray_font	(max_keyword+13) /*string number for the default |gray_font|*/ 
@d logo_font_name	(max_keyword+14) /*string number for the font with \MF\ logo*/ 
@d small_logo	(max_keyword+15) /*string number for `\.{METAFONT}'*/ 
@d home_font_area	(max_keyword+16) /*string number for system-dependent font area*/ 

@<Initialize the strings@>=
l=3;init_str3('.')('g')('f')(gf_ext);@/
l=4;init_str4('.')('d')('v')('i')(dvi_ext);@/
l=4;init_str4('.')('t')('f')('m')(tfm_ext);@/
l=7;init_str7(' ')(' ')('P')('a')('g')('e')(' ')(page_header);@/
l=12;init_str12(' ')(' ')('C')('h')('a')('r')('a')('c')('t')('e')('r')(' ')
  (char_header);@/
l=6;init_str6(' ')(' ')('E')('x')('t')(' ')(ext_header);@/
l=4;init_str4(' ')(' ')('`')('`')(left_quotes);@/
l=2;init_str2('\'')('\'')(right_quotes);@/
l=3;init_str3(' ')('=')(' ')(equals_sign);@/
l=4;init_str4(' ')('+')(' ')('(')(plus_sign);@/
l=4;init_str4('c')('m')('r')('8')(default_title_font);@/
l=6;init_str6('c')('m')('t')('t')('1')('0')(default_label_font);@/
l=4;init_str4('g')('r')('a')('y')(default_gray_font);@/
l=5;init_str5('l')('o')('g')('o')('8')(logo_font_name);@/
l=8;init_str8('M')('E')('T')('A')('F')('O')('N')('T')(small_logo);

@ If an \\{xxx} command has just been encountered in the \.{GF} file,
the following procedure interprets its keyword. More precisely, we assume
that |cur_gf| contains an op-code byte just read from the \.{GF} file,
where |xxx1 <= cur_gf <= no_op|. The |interpret_xxx| procedure will read the
rest of the command, in the following way:
\smallskip
\item{1)} If |cur_gf| is |no_op| or |yyy|, or if it's an \\{xxx} command with
an unknown keyword, the bytes are simply read and ignored, and the
value |no_operation| is returned.

\item{2)} If |cur_gf| is an \\{xxx} command (either |xxx1| or $\cdots$
or |xxx4|), and if the associated string matches a keyword exactly,
the string number of that keyword is returned (e.g., |rule_thickness_code|).

\item{3)} If |cur_gf| is an \\{xxx} command whose string begins with
keyword and space, the string number of that keyword is returned, and
the remainder of the string is put into the string pool (where it will be
string number |cur_string|. Exception: If the keyword is |null_string|,
the character immediately following the blank space is put into the
global variable |label_type|, and the remaining characters go into the
string pool.

\smallskip\noindent
In all cases, |cur_gf| will then be reset to the op-code byte that
immediately follows the original command.

@d no_operation	(max_keyword+1)

@<Types ...@>=
typedef uint8_t keyword_code;

@ @<Glob...@>=
eight_bits @!cur_gf; /*the byte most recently read from |gf_file|*/ 
str_number @!cur_string; /*the string following a keyword and space*/ 
eight_bits @!label_type; /*the character following a null keyword and space*/ 

@ We will be using this procedure when reading the \.{GF} file just
after the preamble and just after |eoc| commands.

@p keyword_code interpret_xxx(void)
{@+
int @!k; /*number of bytes in an \\{xxx} command*/ 
int @!j; /*number of bytes read so far*/ 
uint8_t @!l; /*length of keyword to check*/ 
keyword_code @!m; /*runs through the list of known keywords*/ 
uint8_t @!n1; /*buffered character being checked*/ 
pool_pointer @!n2; /*pool character being checked*/ 
keyword_code @!c; /*the result to return*/ 
c=no_operation;cur_string=null_string;
switch (cur_gf) {
case no_op: goto done;
case yyy: {@+k=signed_quad();goto done;
  } 
case xxx1: k=get_byte();@+break;
case xxx2: k=get_two_bytes();@+break;
case xxx3: k=get_three_bytes();@+break;
case xxx4: k=signed_quad();
}  /*there are no other cases*/ 
@<Read the next |k| characters of the \.{GF} file; change |c| and |goto done| if a
keyword is recognized@>;
done: cur_gf=get_byte();return c;
} 

@ @<Read the next |k|...@>=
j=0;@+if (k < 2) goto not_found;
loop@+{@+l=j;
  if (j==k) goto done1;
  if (j==longest_keyword) goto not_found;
  incr(j);buffer[j]=get_byte();
  if (buffer[j]==' ') goto done1;
  } 
done1: @<If the keyword in |buffer[1..l]| is known, change |c| and |goto done|@>;
not_found: while (j < k) 
  {@+incr(j);cur_gf=get_byte();
  } 

@ @<If the keyword...@>=
for (m=null_string; m<=max_keyword; m++) if (length(m)==l) 
  {@+n1=0;n2=str_start[m];
  while ((n1 < l)&&(buffer[n1+1]==str_pool[n2])) 
    {@+incr(n1);incr(n2);
    } 
  if (n1==l) 
    {@+c=m;
    if (m==null_string) 
      {@+incr(j);label_type=get_byte();
      } 
    str_room(k-j);
    while (j < k) 
      {@+incr(j);append_char(get_byte());
      } 
    cur_string=make_string();goto done;
    } 
  } 

@ When an \\{xxx} command takes a numeric argument, |get_yyy| reads
that argument and puts the following byte into |cur_gf|.

@p scaled get_yyy(void)
{@+scaled @!v; /*value just read*/ 
if (cur_gf!=yyy) return 0;
else{@+v=signed_quad();cur_gf=get_byte();return v;
  } 
} 

@ A simpler method is used for special commands between |boc| and |eoc|,
since \.{GFtoDVI} doesn't even look at them.

@p void skip_nop(void)
{@+
int @!k; /*number of bytes in an \\{xxx} command*/ 
int @!j; /*number of bytes read so far*/ 
switch (cur_gf) {
case no_op: goto done;
case yyy: {@+k=signed_quad();goto done;
  } 
case xxx1: k=get_byte();@+break;
case xxx2: k=get_two_bytes();@+break;
case xxx3: k=get_three_bytes();@+break;
case xxx4: k=signed_quad();
}  /*there are no other cases*/ 
for (j=1; j<=k; j++) cur_gf=get_byte();
done: cur_gf=get_byte();
} 

@*File names.
It's time now to fret about file names. \.{GFtoDVI} uses the conventions of
\TeX\ and \MF\ to convert file names into strings that can be used to open
files. Three routines called |begin_name|, |more_name|, and |end_name| are
involved, so that the system-dependent parts of file naming conventions are
isolated from the system-independent ways in which file names are used.
(See the \TeX\ or \MF\ program listing for further explanation.)
@^system dependencies@>

@<Glob...@>=
str_number @!cur_name; /*name of file just scanned*/ 
str_number @!cur_area; /*file area just scanned, or |null_string|*/ 
str_number @!cur_ext; /*file extension just scanned, or |null_string|*/ 

@ The file names we shall deal with for illustrative purposes have the
following structure:  If the name contains `\.>' or `\.:', the file area
consists of all characters up to and including the final such character;
otherwise the file area is null.  If the remaining file name contains
`\..', the file extension consists of all such characters from the first
remaining `\..' to the end, otherwise the file extension is null.
@^system dependencies@>

We can scan such file names easily by using two global variables that keep track
of the occurrences of area and extension delimiters:

@<Glob...@>=
pool_pointer @!area_delimiter; /*the most recent `\.>' or `\.:', if any*/ 
pool_pointer @!ext_delimiter; /*the relevant `\..', if any*/ 

@ Font metric files whose areas are not given
explicitly are assumed to appear in a standard system area called
|home_font_area|.  This system area name will, of course, vary from place
to place. The program here sets it to `\.{TeXfonts:}'.
@^system dependencies@>
@.TeXfonts@>

@<Initialize the strings@>=
l=9;init_str9('T')('e')('X')('f')('o')('n')('t')('s')(':')(home_font_area);@/

@ Here now is the first of the system-dependent routines for file name scanning.
@^system dependencies@>

@p void begin_name(void)
{@+area_delimiter=0;ext_delimiter=0;
} 

@ And here's the second.
@^system dependencies@>

@p bool more_name(ASCII_code @!c)
{@+if (c==' ') return false;
else{@+if ((c=='>')||(c==':')) 
    {@+area_delimiter=pool_ptr;ext_delimiter=0;
    } 
  else if ((c=='.')&&(ext_delimiter==0)) ext_delimiter=pool_ptr;
  str_room(1);append_char(c); /*contribute |c| to the current string*/ 
  return true;
  } 
} 

@ The third.
@^system dependencies@>

@p void end_name(void)
{@+if (str_ptr+3 > max_strings) 
  abort("Too many strings!");
@.Too many strings@>
if (area_delimiter==0) cur_area=null_string;
else{@+cur_area=str_ptr;incr(str_ptr);
  str_start[str_ptr]=area_delimiter+1;
  } 
if (ext_delimiter==0) 
  {@+cur_ext=null_string;cur_name=make_string();
  } 
else{@+cur_name=str_ptr;incr(str_ptr);
  str_start[str_ptr]=ext_delimiter;cur_ext=make_string();
  } 
} 

@ Another system-dependent routine is needed to convert three strings
into the |name_of_file| value that is used to open files. The present code
allows both lowercase and uppercase letters in the file name.
@^system dependencies@>

@d append_to_name(X)	{@+c=X;incr(k);
  if (k <= file_name_size) name_of_file[k]=xchr[c];
  } 

@p void pack_file_name(str_number @!n, str_number @!a, str_number @!e)
{@+int k; /*number of positions filled in |name_of_file|*/ 
ASCII_code @!c; /*character being packed*/ 
int @!j; /*index into |str_pool|*/ 
uint8_t @!name_length; /*number of characters packed*/ 
k=0;
for (j=str_start[a]; j<=str_start[a+1]-1; j++) append_to_name(str_pool[j]);
for (j=str_start[n]; j<=str_start[n+1]-1; j++) append_to_name(str_pool[j]);
for (j=str_start[e]; j<=str_start[e+1]-1; j++) append_to_name(str_pool[j]);
if (k <= file_name_size) name_length=k;@+else name_length=file_name_size;
name_of_file[name_length+1]=0;
} 

@ Now let's consider the routines by which \.{GFtoDVI} deals with file names
in a system-independent manner.
The global variable |job_name| contains the \.{GF} file name that is
being input. This name is extended by `\.{dvi}'
in order to make the name of the output file.

@<Glob...@>=
str_number @!job_name; /*principal file name*/ 

@ The |start_gf| procedure prompts the user for the name of the generic
font file to be input. It opens the file, making sure that some input is
present; then it opens the output file.

Although this routine is system-independent, it should probably be
modified to take the file name from the command line (without an initial
prompt), on systems that permit such things.

@p void start_gf(void)
{@+
loop@+{@+print_nl("GF file name: ");input_ln();
@.GF file name@>
  buf_ptr=0;buffer[line_length]='?';
  while (buffer[buf_ptr]==' ') incr(buf_ptr);
  if (buf_ptr < line_length) 
    {@+@<Scan the file name in the buffer@>;
    if (cur_ext==null_string) cur_ext=gf_ext;
    pack_file_name(cur_name, cur_area, cur_ext);open_gf_file();
    if (!eof(gf_file)) goto found;
    print_nl("Oops... I can't find file ");print(name_of_file);
@.Oops...@>
@.I can't find...@>
    } 
  } 
found: job_name=cur_name;pack_file_name(job_name, null_string, dvi_ext);
open_dvi_file();
} 

@ @<Scan the file name in the buffer@>=
if (buffer[line_length-1]=='/') 
  {@+interaction=true;decr(line_length);
  } 
begin_name();
loop@+{@+if (buf_ptr==line_length) goto done;
  if (!more_name(buffer[buf_ptr])) goto done;
  incr(buf_ptr);
  } 
done: end_name()

@ Special instructions found near the beginning of the \.{GF} file might
change the names, areas, and ``at'' sizes of the fonts that \.{GFtoDVI}
will be using. But when we reach the first |boc| instruction, we input
all of the \.{TFM} files. The global variable |interaction| is set |true|
if a |'/'| was removed at the end of the file name; this means that the
user will have a chance to issue special instructions online just before
the fonts are loaded.

@d check_fonts	@+if (fonts_not_loaded) load_fonts()

@<Glob...@>=
bool @!interaction; /*is the user allowed to type specials online?*/ 
bool @!fonts_not_loaded; /*have the \.{TFM} files still not been input?*/ 
str_number @!font_name0[logo_font-title_font+1], *const @!font_name = @!font_name0-title_font; /*current font names*/ 
str_number @!font_area0[logo_font-title_font+1], *const @!font_area = @!font_area0-title_font; /*current font areas*/ 
scaled @!font_at0[logo_font-title_font+1], *const @!font_at = @!font_at0-title_font; /*current font ``at'' sizes*/ 

@ @<Set init...@>=
interaction=false;fonts_not_loaded=true;
font_name[title_font]=default_title_font;
font_name[label_font]=default_label_font;
font_name[gray_font]=default_gray_font;
font_name[slant_font]=null_string;
font_name[logo_font]=logo_font_name;
for (k=title_font; k<=logo_font; k++) 
  {@+font_area[k]=null_string;font_at[k]=0;
  } 

@ After the following procedure has been performed, there will be no
turning back; the fonts will have been firmly established in
\.{GFtoDVI}'s memory.

@<Declare the procedure called |load_fonts|@>=
void load_fonts(void)
{@+
internal_font_number @!f;
four_quarters @!i; /*font information word*/ 
int @!j, @!k, @!v; /*registers for initializing font tables*/ 
uint8_t @!m; /*keyword found*/ 
uint8_t @!n1; /*buffered character being checked*/ 
pool_pointer @!n2; /*pool character being checked*/ 
if (interaction) @<Get online special input@>;
fonts_not_loaded=false;
for (f=title_font; f<=logo_font; f++) 
 if ((f!=slant_font)||(length(font_name[f]) > 0)) 
  {@+if (length(font_area[f])==0) font_area[f]=home_font_area;
  pack_file_name(font_name[f], font_area[f], tfm_ext);
  open_tfm_file();read_font_info(f, font_at[f]);
  if (font_area[f]==home_font_area) font_area[f]=null_string;
  dvi_font_def(f); /*put the font name in the \.{DVI} file*/ 
  } 
@<Initialize global variables that depend on the font data@>;
} 

@ @<Get online special input@>=
loop@+{@+not_found: print_nl("Special font substitution: ");
@.Special font subst...@>
  resume: input_ln();
  if (line_length==0) goto done;
  @<Search buffer for valid keyword; if successful, |goto found|@>;
  print("Please say, e.g., \"grayfont foo\" or \"slantfontarea baz\".");
  goto not_found;
  found: @<Update the font name or area@>;
  print("OK; any more? ");goto resume;
  } 
done: 

@ @<Search buffer for valid keyword; if successful, |goto found|@>=
buf_ptr=0;buffer[line_length]=' ';
while (buffer[buf_ptr]!=' ') incr(buf_ptr);
for (m=title_font; m<=slant_font+area_code; m++) if (length(m)==buf_ptr) 
  {@+n1=0;n2=str_start[m];
  while ((n1 < buf_ptr)&&(buffer[n1]==str_pool[n2])) 
    {@+incr(n1);incr(n2);
    } 
  if (n1==buf_ptr) goto found;
  } 

@ @<Update the font name or area@>=
incr(buf_ptr);str_room(line_length-buf_ptr);
while (buf_ptr < line_length) 
  {@+append_char(buffer[buf_ptr]);incr(buf_ptr);
  } 
if (m > area_code) font_area[m-area_code]=make_string();
else{@+font_name[m]=make_string();font_area[m]=null_string;
  font_at[m]=0;
  } 
init_str_ptr=str_ptr

@*Shipping pages out.
The following routines are used to write the \.{DVI} file. They have
been copied from \TeX, but simplified; we don't have to handle
nearly as much generality as \TeX\ does.

Statistics about the entire set of pages that will be shipped out must be
reported in the \.{DVI} postamble. The global variables |total_pages|,
|max_v|, |max_h|, and |last_bop| are used to record this information.

@<Glob...@>=
int @!total_pages; /*the number of pages that have been shipped out*/ 
scaled @!max_v; /*maximum height-plus-depth of pages shipped so far*/ 
scaled @!max_h; /*maximum width of pages shipped so far*/ 
int @!last_bop; /*location of previous |bop| in the \.{DVI} output*/ 

@ @<Set init...@>=
total_pages=0;max_v=0;max_h=0;last_bop=-1;

@ The \.{DVI} bytes are output to a buffer instead of being written directly
to the output file. This makes it possible to reduce the overhead of
subroutine calls.

The output buffer is divided into two parts of equal size; the bytes found
in |dvi_buf[0 dotdot half_buf-1]| constitute the first half, and those in
|dvi_buf[half_buf dotdot dvi_buf_size-1]| constitute the second. The global
variable |dvi_ptr| points to the position that will receive the next
output byte. When |dvi_ptr| reaches |dvi_limit|, which is always equal
to one of the two values |half_buf| or |dvi_buf_size|, the half buffer that
is about to be invaded next is sent to the output and |dvi_limit| is
changed to its other value. Thus, there is always at least a half buffer's
worth of information present, except at the very beginning of the job.

Bytes of the \.{DVI} file are numbered sequentially starting with 0;
the next byte to be generated will be number |dvi_offset+dvi_ptr|.

@<Types ...@>=
typedef uint16_t dvi_index; /*an index into the output buffer*/ 

@ Some systems may find it more efficient to make |dvi_buf| a ||
array, since output of four bytes at once may be facilitated.
@^system dependencies@>

@<Glob...@>=
eight_bits @!dvi_buf[dvi_buf_size+1]; /*buffer for \.{DVI} output*/ 
dvi_index @!half_buf; /*half of |dvi_buf_size|*/ 
dvi_index @!dvi_limit; /*end of the current half buffer*/ 
dvi_index @!dvi_ptr; /*the next available buffer address*/ 
int @!dvi_offset; /*|dvi_buf_size| times the number of times the
  output buffer has been fully emptied*/ 

@ Initially the buffer is all in one piece; we will output half of it only
after it first fills up.

@<Set init...@>=
half_buf=dvi_buf_size/2;dvi_limit=dvi_buf_size;dvi_ptr=0;
dvi_offset=0;

@ The actual output of |dvi_buf[a dotdot b]| to |dvi_file| is performed by calling
|write_dvi(a, b)|. It is safe to assume that |a| and |b+1| will both be
multiples of 4 when |write_dvi(a, b)| is called; therefore it is possible on
many machines to use efficient methods to pack four bytes per word and to
output an array of words with one system call.
@^system dependencies@>

@p void write_dvi(dvi_index @!a, dvi_index @!b)
{@+int k;
for (k=a; k<=b; k++) write(dvi_file, "%c", dvi_buf[k]);
} 

@ To put a byte in the buffer without paying the cost of invoking a procedure
each time, we use the macro |dvi_out|.

@d dvi_out(X)	@+{@+dvi_buf[dvi_ptr]=X;incr(dvi_ptr);
  if (dvi_ptr==dvi_limit) dvi_swap();
  } 

@p void dvi_swap(void) /*outputs half of the buffer*/ 
{@+if (dvi_limit==dvi_buf_size) 
  {@+write_dvi(0, half_buf-1);dvi_limit=half_buf;
  dvi_offset=dvi_offset+dvi_buf_size;dvi_ptr=0;
  } 
else{@+write_dvi(half_buf, dvi_buf_size-1);dvi_limit=dvi_buf_size;
  } 
} 

@ Here is how we clean out the buffer when \TeX\ is all through; |dvi_ptr|
will be a multiple of~4.

@<Empty the last bytes out of |dvi_buf|@>=
if (dvi_limit==half_buf) write_dvi(half_buf, dvi_buf_size-1);
if (dvi_ptr > 0) write_dvi(0, dvi_ptr-1)

@ The |dvi_four| procedure outputs four bytes in two's complement notation,
without risking arithmetic overflow.

@p void dvi_four(int @!x)
{@+if (x >= 0) dvi_out(x/0100000000)@;
else{@+x=x+010000000000;
  x=x+010000000000;
  dvi_out((x/0100000000)+128);
  } 
x=x%0100000000;dvi_out(x/0200000);
x=x%0200000;dvi_out(x/0400);
dvi_out(x%0400);
} 

@ Here's a procedure that outputs a font definition.

@d select_font(X)	dvi_out(fnt_num_0+X) /*set current font to \#*/ 

@p void dvi_font_def(internal_font_number @!f)
{@+int k; /*index into |str_pool|*/ 
dvi_out(fnt_def1);
dvi_out(f);@/
dvi_out(qo(font_check[f].b0));
dvi_out(qo(font_check[f].b1));
dvi_out(qo(font_check[f].b2));
dvi_out(qo(font_check[f].b3));@/
dvi_four(font_size[f]);
dvi_four(font_dsize[f]);@/
dvi_out(length(font_area[f]));
dvi_out(length(font_name[f]));
@<Output the font name whose internal number is |f|@>;
} @/
@t\4@>@<Declare the procedure called |load_fonts|@>@;

@ @<Output the font name whose internal number is |f|@>=
for (k=str_start[font_area[f]]; k<=str_start[font_area[f]+1]-1; k++) 
  dvi_out(str_pool[k]);
for (k=str_start[font_name[f]]; k<=str_start[font_name[f]+1]-1; k++) 
  dvi_out(str_pool[k])

@ The |typeset| subroutine typesets any eight-bit character.

@p void typeset(eight_bits @!c)
{@+if (c >= 128) dvi_out(set1);
dvi_out(c);
} 

@ The |dvi_scaled| subroutine takes a |double| value |x| and outputs
a decimal approximation to |x/(double)unity|, correct to one decimal place.

@p void dvi_scaled(double @!x)
{@+int @!n; /*an integer approximation to |10*x/(double)unity|*/ 
int @!m; /*the integer part of the answer*/ 
int @!k; /*the number of digits in |m|*/ 
n=round(x/(double)6553.6);
if (n < 0) 
  {@+dvi_out('-');n=-n;
  } 
m=n/10;k=0;
@/do@+{incr(k);buffer[k]=(m%10)+'0';m=m/10;
}@+ while (!(m==0));
@/do@+{dvi_out(buffer[k]);decr(k);
}@+ while (!(k==0));
if (n%10!=0) 
  {@+dvi_out('.');dvi_out((n%10)+'0');
  } 
} 

@ At the end of the program, we must finish things off by writing the
post\-amble. An integer variable~|k| will be declared for use by this routine.

@<Finish the \.{DVI} file and |goto final_end|@>=
{@+dvi_out(post); /*beginning of the postamble*/ 
dvi_four(last_bop);last_bop=dvi_offset+dvi_ptr-5; /*|post| location*/ 
dvi_four(25400000);dvi_four(473628672); /*conversion ratio for sp*/ 
dvi_four(1000); /*magnification factor*/ 
dvi_four(max_v);dvi_four(max_h);@/
dvi_out(0);dvi_out(3); /*`\\{max\_push}' is said to be 3*/ @/
dvi_out(total_pages/256);dvi_out(total_pages%256);@/
if (!fonts_not_loaded) 
  for (k=title_font; k<=logo_font; k++) 
    if (length(font_name[k]) > 0) dvi_font_def(k);
dvi_out(post_post);dvi_four(last_bop);dvi_out(dvi_id_byte);@/
k=4+((dvi_buf_size-dvi_ptr)%4); /*the number of 223's*/ 
while (k > 0) 
  {@+dvi_out(223);decr(k);
  } 
@<Empty the last bytes out of |dvi_buf|@>;
exit(0);
} 

@*Rudimentary typesetting.
One of \.{GFtoDVI}'s little duties is to be a mini-\TeX: It must be able
to typeset the equivalent of `\.{\\hbox\{}$\langle$string$\rangle$\.\}' for
a given string of ASCII characters, using either the title font or the
label font.

The |hbox| procedure does this. The width, height, and depth of the
box defined by string~|s| in font~|f| are computed in global variables
|box_width|, |box_height|, and |box_depth|.

The task would be trivial if it weren't for ligatures and kerns, which
are implemented here in full generality. (Infinite looping is possible
if the \.{TFM} file is malformed; \.{TFtoPL} will diagnose such problems.)

We assume that |' '| is a space character; character code 040 will not
be typeset unless it is accessed via a ligature.

If parameter |send_it| is |false|, we merely want to know the box dimensions.
Otherwise typesetting commands are also sent to
the \.{DVI} file; we assume in this case that font |f| has already been
selected in the \.{DVI} file as the current font.

@d set_cur_r	if (k < end_k) cur_r=qi(str_pool[k]);
    else cur_r=bchar

@p void hbox(str_number @!s, internal_font_number @!f, bool @!send_it)
{@+
pool_pointer @!k, @!end_k, @!max_k; /*indices into |str_pool|*/ 
four_quarters @!i, @!j; /*font information words*/ 
uint16_t @!cur_l; /*character to the left of the ``cursor''*/ 
uint16_t @!cur_r; /*character to the right of the ``cursor''*/ 
uint16_t @!bchar; /*right boundary character*/ 
uint8_t @!stack_ptr; /*number of entries on |lig_stack|*/ 
font_index @!l; /*pointer to lig/kern instruction*/ 
scaled @!kern_amount; /*extra space to be typeset*/ 
eight_bits @!hd; /*height and depth indices for a character*/ 
scaled @!x; /*temporary register*/ 
ASCII_code @!save_c; /*character temporarily blanked out*/ 
box_width=0;box_height=0;box_depth=0;@/
k=str_start[s];max_k=str_start[s+1];
save_c=str_pool[max_k];str_pool[max_k]=' ';
while (k < max_k) 
  {@+if (str_pool[k]==' ') @<Typeset a space in font |f| and advance~|k|@>@;
  else{@+end_k=k;
    @/do@+{incr(end_k);}@+ while (!(str_pool[end_k]==' '));
    kern_amount=0;cur_l=256;stack_ptr=0;bchar=font_bchar[f];
    set_cur_r;suppress_lig=false;
resume: @<If there's a ligature or kern at the cursor position, update the cursor
data structures, possibly advancing~|k|; continue until the cursor wants to move right@>;
    @<Typeset character |cur_l|, if it exists in the font; also append an optional
kern@>;
    @<Move the cursor to the right and |goto continue|, if there's more work to do
in the current word@>;
    }  /*now |k==end_k|*/ 
  } 
str_pool[max_k]=save_c;
} 

@ @<Glob...@>=
scaled @!box_width; /*width of box constructed by |hbox|*/ 
scaled @!box_height; /*height of box constructed by |hbox|*/ 
scaled @!box_depth; /*depth of box constructed by |hbox|*/ 
quarterword @!lig_stack0[lig_lookahead], *const @!lig_stack = @!lig_stack0-1; /*inserted ligature chars*/ 
four_quarters @!dummy_info; /*fake |char_info| for nonexistent character*/ 
bool @!suppress_lig; /*should we bypass checking for ligatures next time?*/ 

@ @<Set init...@>=
dummy_info.b0=qi(0);dummy_info.b1=qi(0);dummy_info.b2=qi(0);
dummy_info.b3=qi(0);

@ @<Typeset a space...@>=
{@+box_width=box_width+space(f);
if (send_it) 
  {@+dvi_out(right4);dvi_four(space(f));
  } 
incr(k);
} 

@ @<If there's a ligature...@>=
if ((cur_l < font_bc[f])||(cur_l > font_ec[f])) 
  {@+i=dummy_info;
  if (cur_l==256) l=bchar_label[f];@+else l=non_address;
  } 
else{@+i=char_info(f)(cur_l);
  if (char_tag(i)!=lig_tag) l=non_address;
  else{@+l=lig_kern_start(f)(i);j=font_info[l].qqqq;
    if (skip_byte(j) > stop_flag) l=lig_kern_restart(f)(j);
    } 
  } 
if (suppress_lig) suppress_lig=false;
else while (l < qi(kern_base[f])) 
  {@+j=font_info[l].qqqq;
  if (next_char(j)==cur_r) if (skip_byte(j) <= stop_flag) 
    if (op_byte(j) >= kern_flag) 
      {@+kern_amount=char_kern(f)(j);goto done;
      } 
    else@<Carry out a ligature operation, updating the cursor structure and possibly
advancing~|k|; |goto continue| if the cursor doesn't advance, otherwise |goto done|@>;
  if (skip_byte(j) >= stop_flag) goto done;
  l=l+skip_byte(j)+1;
  } 
done: 

@ At this point |i| contains |char_info| for |cur_l|.

@<Typeset character...@>=
if (char_exists(i)) 
  {@+box_width=box_width+char_width(f)(i)+kern_amount;@/
  hd=height_depth(i);
  x=char_height(f)(hd);
  if (x > box_height) box_height=x;
  x=char_depth(f)(hd);
  if (x > box_depth) box_depth=x;
  if (send_it) 
    {@+typeset(cur_l);
    if (kern_amount!=0) 
      {@+dvi_out(right4);dvi_four(kern_amount);
      } 
    } 
  kern_amount=0;
  } 

@ @d pop_stack	{@+decr(stack_ptr);
    if (stack_ptr > 0) cur_r=lig_stack[stack_ptr];
    else set_cur_r;
    } 

@<Carry out a ligature operation, updating the cursor structure...@>=
{@+switch (op_byte(j)) {
case 1: case 5: cur_l=qo(rem_byte(j));@+break;
case 2: case 6: {@+cur_r=rem_byte(j);
  if (stack_ptr==0) 
    {@+stack_ptr=1;
    if (k < end_k) incr(k); /*a non-space character is consumed*/ 
    else bchar=non_char; /*the right boundary character is consumed*/ 
    } 
  lig_stack[stack_ptr]=cur_r;
  } @+break;
case 3: case 7: case 11: {@+cur_r=rem_byte(j);incr(stack_ptr);lig_stack[stack_ptr]=cur_r;
  if (op_byte(j)==11) suppress_lig=true;
  } @+break;
default:{@+cur_l=qo(rem_byte(j));
  if (stack_ptr > 0) pop_stack@;
  else if (k==end_k) goto done;
  else{@+incr(k);set_cur_r;
    } 
  } 
} 
if (op_byte(j) > 3) goto done;
goto resume;
} 

@ @<Move the cursor to the right and |goto continue|...@>=
cur_l=qo(cur_r);
if (stack_ptr > 0) 
  {@+pop_stack;goto resume;
  } 
if (k < end_k) 
  {@+incr(k);set_cur_r;goto resume;
  } 

@*Gray fonts.
A proof diagram constructed by \.{GFtoDVI}
can be regarded as an array of rectangles, where each rectangle is either
blank or filled with a special symbol that we shall call $x$. A blank
rectangle represents a white pixel, while $x$ represents a black pixel.
Additional labels and reference lines are often superimposed on this
array of rectangles; hence it is usually best to choose a symbol $x$ that
has a somewhat gray appearance, although any symbol can actually be used.

In order to construct such proofs, \.{GFtoDVI} needs to work with
a special type of font known as a ``gray font''; it's possible to
obtain a wide variety of different sorts of proofs by using different
sorts of gray fonts. The next few paragraphs explain exactly what gray
fonts are supposed to contain, in case you want to design your own.
@^gray fonts@>

@ The simplest gray font contains only two characters, namely $x$
and another symbol that is used for dots that identify key points.
If proofs with relatively large pixels are desired, a two-character
gray font is all that's needed. However, if the pixel size is to be
relatively small, practical considerations make a two-character
font too inefficient, since it requires the typesetting of tens
of thousands of tiny little characters; printing device drivers
rarely work very well when they are presented with data that is
so different from ordinary text. Therefore a gray font with small
pixels usually has a number of characters that replicate $x$ in
such a way that comparatively few characters actually need to be
typeset.

Since many printing devices are not able to cope with
arbitrarily large or complex characters, it is not possible for a
single gray font to work well on all machines. In fact,
$x$ must have a width that is an integer multiple of the printing
device's unit of horizontal position, since rounding the positions of grey
characters would otherwise produce unsightly streaks on proof output.
Thus, there is no way to make the gray font as device-independent as
the rest of the system, in the sense that we would expect approximately
identical output on machines with different resolution. Fortunately,
proof sheets are rarely considered to be final documents; hence
\.{GFtoDVI} is set up to provide results that adapt suitably to
local conditions.

@ With such constraints understood, we can now take a look at what
\.{GFtoDVI} expects to see in a gray font. The character~$x$ always
appears in position~1. It must have positive height~$h$ and positive
width~$w$; its depth and italic correction are ignored.

Positions 2--120 of a gray font are reserved for special combinations
of $x$'s and blanks, stacked on top of each other. None of these character
codes need be present in the font; but if they are, the slots should be
occupied by characters of width~$w$ that have certain configurations of
$x$'s and blanks, prescribed for each character position. For example,
position~3 of the font should either contain no character at all,
or it should contain a character consisting of two $x$'s, one above
the other; one of these $x$'s should appear immediately above the
baseline, and the other should appear immediately below.

It will be convenient to use a horizontal notation like `\.{XOXXO}'
to stand for a vertical stack of $x$'s and blanks. The convention
will be that the stack is built from bottom to top, and the topmost
rectangle should sit on the baseline. Thus, `\.{XOXXO}' stands
actually for a character of depth~$4h$ that looks like this:
$$\vcenter{\halign{\hfil#\hfil\cr
blank\cr
$x$\rlap{\qquad\raise8pt\hbox{\smash{\hbox{$\longleftarrow$ baseline}}}}\cr
$x$\cr
blank\cr
$x$\cr
}}$$
(We use a horizontal notation instead of a vertical one in this explanation,
because column
vectors take too much space, and because the horizontal notation corresponds
to binary numbers in a convenient way.)

Positions 1--63 of a gray font are reserved for the patterns \.X, \.{XO},
\.{XX}, \.{XOO}, \.{XOX}, \dots, \.{XXXXXX}, just as in the normal
binary notation of the numbers 1--63. Positions 64--70 are reserved for
the special patterns \.{XOOOOOO}, \.{XXOOOOO}, \dots, \.{XXXXXXO},
\.{XXXXXXX} of length seven; positions 71--78 are, similarly, reserved for
the length-eight patterns \.{XOOOOOOO} through \.{XXXXXXXX}. The
length-nine patterns \.{XOOOOOOOO} through \.{XXXXXXXXX} are assigned
to positions 79--87, the length-ten patterns to positions 88--97,
the length-eleven patterns to positions 98--108, and the length-twelve
patterns to positions 109--120.

The following program sets a global array |c[1 dotdot 120]| to the bit patterns
just described. Another array |d[1 dotdot 120]| is set to contain only the next
higher bit; this determines the depth of the corresponding character.

@<Set init...@>=
c[1]=1;d[1]=2;two_to_the[0]=1;m=1;
for (k=1; k<=13; k++) two_to_the[k]=2*two_to_the[k-1];
for (k=2; k<=6; k++) @<Add a full set of |k|-bit characters@>;
for (k=7; k<=12; k++) @<Add special |k|-bit characters of the form \.{X..XO..O}@>;

@ @<Glob...@>=
uint16_t @!c0[120], *const @!c = @!c0-1; /*bit patterns for a gray font*/ 
uint16_t @!d0[120], *const @!d = @!d0-1; /*the superleading bits*/ 
uint16_t @!two_to_the[14]; /*powers of 2*/ 

@ @<Add a full set of |k|-bit...@>=
{@+n=two_to_the[k-1];
for (j=0; j<=n-1; j++) 
  {@+incr(m);c[m]=m;d[m]=n+n;
  } 
} 

@ @<Add special |k|-bit...@>=
{@+n=two_to_the[k-1];
for (j=k; j>=1; j--) 
  {@+incr(m);d[m]=n+n;
  if (j==k) c[m]=n;
  else c[m]=c[m-1]+two_to_the[j-1];
  } 
} 

@ Position 0 of a gray font is reserved for the ``dot'' character, which
should have positive height~$h'$ and positive width~$w'$. When \.{GFtoDVI}
wants to put a dot at some place $(x,y)$ on the figure, it positions
the dot character so that its reference point is at $(x,y)$. The
dot will be considered to occupy a rectangle $(x+\delta,y+\epsilon)$
for $-w'\leq\delta\leq w'$ and $-h'\leq\epsilon\leq h'$; the rectangular
box for a label will butt up against the rectangle enclosing the dot.

@ All other character positions of a gray font (namely, positions 121--255)
are unreserved, in the sense that they have no predefined meaning.
But \.{GFtoDVI} may access them via the ``character list'' feature of
\.{TFM} files, starting with any of the characters in positions
1--120. In such a case each succeeding character in a list should be
equivalent to two of its predecessors, horizontally adjacent to each other.
For example, in a character list like
$$53,\;121,\;122,\;123$$
character 121 will stand for two 53's, character 122 for two 121's (i.e.,
four 53's), and character 123 for two 122's (i.e., eight 53's). Since
position~53 contains the pattern \.{XXOXOX}, character~123 in this example
would have height~$h$, depth~$5h$, and width~$8w$, and it would stand for
the pattern
$$\vcenter{\halign{&$\hfil#\hfil$\cr
x&x&x&x&x&x&x&x\cr
&&&&&&&\cr
x&x&x&x&x&x&x&x\cr
&&&&&&&\cr
x&x&x&x&x&x&x&x\cr
x&x&x&x&x&x&x&x\cr}}$$
Such a pattern is, of course, rather unlikely to occur in a \.{GF} file,
but \.{GFtoDVI} would be able to use if it were present. Designers
of gray fonts should provide characters only for patterns that they think
will occur often enough to make the doubling worthwhile. For example,
the character in position 120 (\.{XXXXXXXXXXXX}), or whatever is the
tallest stack of $x$'s present in the font, is a natural candidate for
repeated doubling.

Here's how \.{GFtoDVI} decides what characters of the gray font will be used,
given a configuration of black and white pixels: If there are no black
pixels, stop. Otherwise look at the top row that contains at least one
black pixel, and the eleven rows that follow. For each such column,
find the largest~$k$ such that $1\leq k\leq120$ and the gray font contains
character~$k$ and the pattern assigned to position~$k$ appears in the
given column. Typeset character $k$ (unless no such character exists)
and erase the corresponding black pixels; use doubled characters,
if they are present in the gray font, if two or more consecutive equal
characters need to be typeset. Repeat the same process on the remaining
configuration, until all the black pixels have been erased.

If all characters in positions 1--120 are present, this process is guaranteed to
take care of at least six rows each time; and it usually takes care of
twelve, since all patterns that contain at most one ``run'' of $x$'s
are present.

@ Fonts have optional parameters, as described in Appendix~F of {\sl The
\TeX book}, and some of these are important in gray fonts. The
slant parameter~$s$, if nonzero, will cause \.{GFtoDVI} to skew its
output; in this case the character $x$ will presumably be a parallelogram
with a corresponding slant, rather than the usual rectangle. \MF's
coordinate $(x,y)$ will appear in physical position $(xw+yhs,yh)$
on the proofsheets.

Parameter number~8 of a gray font specifies the thickness of rules
that go on the proofs. If this parameter is zero, \TeX's default
rule thickness (0.4\thinspace pt) will be used.

The other parameters of a gray font are ignored by \.{GFtoDVI}, but
it is conventional to set the font space parameter to~$w$ and the
xheight parameter to~$h$.

@ For best results the designer of a gray font should choose $h$ and~$w$
so that the user's \.{DVI}-to-hardcopy software will not make any
rounding errors. Furthermore, the dot should be an even number~$2m$ of
pixels in diameter, and the rule thickness should work out to an
even number~$2n$ of pixels; then the dots and rules will be centered on
the correct positions, in case of integer coordinates. Gray fonts
are almost always intended for particular output devices, even though
`\.{DVI}' stands for `device independent'; we use \.{DVI} files for \MF\
proofs chiefly because software to print \.{DVI} files is already in place.

@*Slant fonts.
\.{GFtoDVI} also makes use of another special type of font, if it is
necessary to typeset slanted rules. The format of such  so-called
``slant fonts'' is quite a bit simpler than the format of gray fonts.

A slant font should contain exactly $n$ characters, in positions 1 to~$n$,
where the character in position~$k$ represents a slanted line $k$ units
tall, starting at the baseline. These lines all have a fixed slant ratio~$s$.

The following simple algorithm is used to typeset a rule that is $m$ units
high: Compute $q=\lceil m/n\rceil$; then typeset $q$~characters of
approximately equal size, namely $(m\bmod q)$ copies of character number
$\lceil m/q\rceil$ and $q-(m\bmod q)$ copies of character number
$\lfloor m/q\rfloor$. For example, if $n=15$ and $m=100$, we have $q=7$;
a 100-unit-high rule will be composed of 7~pieces, using characters
14,~14, 14, 14, 14, 15,~15.

@<Glob...@>=
double @!rule_slant; /*the slant ratio $s$ in the slant font,
  or zero if there is no slant font*/ 
int @!slant_n; /*the number of characters in the slant font*/ 
double @!slant_unit; /*the number of scaled points in the slant font unit*/ 
double @!slant_reported; /*invalid slant ratio reported to the user*/ 

@ \.{GFtoDVI} looks only at the height of character $n$, so the \.{TFM} file
need not be accurate about the heights of the other characters. (This is
fortunate, since \.{TFM} format allows at most 16 different heights per font.)

The width of character~$k$ should be $k/n$ times $s$ times the height of
character~$n$.

The slant parameter of a slant file should be $s$. It is customary to
set the |default_rule_thickness| parameter (number~8) to the thickness of
the slanted rules, but \.{GFtoDVI} doesn't look at it.

@ For best results on a particular output device, it is usually wise to
choose the `unit' in the above discussion to be an integer number of pixels,
and to make it no larger than the default rule thickness in the gray font
being used.

@ @<Initialize glob...@>=
if (length(font_name[slant_font])==0) rule_slant=0.0;
else{@+rule_slant=slant(slant_font)/(double)unity;
  slant_n=font_ec[slant_font];
  i=char_info(slant_font)(slant_n);
  slant_unit=char_height(slant_font)(height_depth(i))/(double)slant_n;
  } 
slant_reported=0.0;

@ The following error message is given when an absent slant has been
requested.

@p void slant_complaint(double @!r)
{@+if (abs(r-slant_reported) > 0.001) 
  {@+print_nl("Sorry, I can't make diagonal rules of slant %10.5f!", r);
@.Sorry, I can't...@>
  slant_reported=r;
  } 
} 

@*Representation of rectangles.
OK---the preliminary spadework has now been done. We're ready at last
to concentrate on \.{GFtoDVI}'s {\sl raison d'\^^Detre}.

One of the most interesting tasks remaining is to make
a ``map'' of the labels that have been allocated.
There usually aren't a great many labels, so we don't need fancy data
structures; but we do make use of linked nodes containing nine fields.
The nodes generally represent rectangular boxes according to the
following conventions:
\smallskip\hang\noindent
|xl|, |xr|, |yt|, and |yb| are the left, right, top, and bottom locations
of a rectangle, expressed in \.{DVI} coordinates. (This program uses
scaled points as \.{DVI} coordinates. Since \.{DVI} coordinates increase
as one moves down the page, |yb| will be greater than |yt|.)
\smallskip\hang\noindent
|xx| and |yy| are the coordinates of the reference point of a box to be
typeset from this node, again in \.{DVI} coordinates.
\smallskip\hang\noindent
|prev| and |next| point to the predecessor and successor of this node.
Sometimes the nodes are singly linked and only |next| is relevant; otherwise
the nodes are doubly linked in order of their |yy| coordinates, so that we
can move down by going to |next|, or up by going to |prev|.
\smallskip\hang\noindent
|info| is the number of a string associated with this node.
\smallskip\noindent

The nine fields of a node appear in nine global arrays.
Null pointers are denoted by |null|, which happens to be zero.

@d null	0

@<Types ...@>=
typedef uint16_t node_pointer;

@ @<Glob...@>=
scaled @!xl0[max_labels], *const @!xl = @!xl0-1, @!xr0[max_labels], *const @!xr = @!xr0-1, @!yt0[max_labels], *const @!yt = @!yt0-1, @!yb0[max_labels], *const @!yb = @!yb0-1; /*boundary coordinates*/ 
scaled @!xx[max_labels+1], @!yy[max_labels+1]; /*reference coordinates*/ 
node_pointer @!prev[max_labels+1], @!next[max_labels+1]; /*links*/ 
str_number @!info0[max_labels], *const @!info = @!info0-1; /*associated strings*/ 
node_pointer @!max_node; /*the largest node in use*/ 
scaled @!max_height; /*greatest difference between |yy| and |yt|*/ 
scaled @!max_depth; /*greatest difference between |yb| and |yy|*/ 


@ It's easy to allocate a new node (unless no more room is left):

@p node_pointer get_avail(void)
{@+incr(max_node);
if (max_node==max_labels) abort("Too many labels and/or rules!");
@.Too many labels@>
return max_node;
} 

@ The doubly linked nodes are sorted by |yy| coordinates so that we don't have
to work too hard to find nearest neighbors or to determine if rectangles overlap.
The first node in the doubly linked rectangle list is always in location~0,
and the last node is always in location |max_labels|; the |yy| coordinates
of these nodes are very small and very large, respectively.

@d end_of_list	max_labels

@<Set init...@>=
yy[0]=-010000000000;yy[end_of_list]=010000000000;

@ The |node_ins| procedure inserts a new rectangle, represented by node~|p|,
into the doubly linked list. There's a second parameter, |q|; node~|q| should
already be in the doubly linked list, preferably with |yy[q]| near |yy[p]|.

@p void node_ins(node_pointer @!p, node_pointer @!q)
{@+node_pointer @!r; /*for tree traversal*/ 
if (yy[p] >= yy[q]) 
  {@+@/do@+{r=q;q=next[q];@+}@+ while (!(yy[p] <= yy[q]));
  next[r]=p;prev[p]=r;next[p]=q;prev[q]=p;
  } 
else{@+@/do@+{r=q;q=prev[q];@+}@+ while (!(yy[p] >= yy[q]));
  prev[r]=p;next[p]=r;prev[p]=q;next[q]=p;
  } 
if (yy[p]-yt[p] > max_height) max_height=yy[p]-yt[p];
if (yb[p]-yy[p] > max_depth) max_depth=yb[p]-yy[p];
} 

@ The data structures need to be initialized for each character in the
\.{GF} file.

@<Initialize variables for the next character@>=
max_node=0;next[0]=end_of_list;prev[end_of_list]=0;
max_height=0;max_depth=0;

@ The |overlap| subroutine determines whether or not the rectangle specified
in node~|p| has a nonempty intersection with some rectangle in the doubly
linked list. Again |q|~is a parameter that gives us a starting point
in the list. We assume that |q!=end_of_list|, so that |next[q]| is meaningful.

@p bool overlap(node_pointer @!p, node_pointer @!q)
{@+
scaled @!y_thresh; /*cutoff value to speed the search*/ 
scaled @!x_left, @!x_right, @!y_top, @!y_bot; /*boundaries to test for overlap*/ 
node_pointer @!r; /*runs through the neighbors of |q|*/ 
x_left=xl[p];x_right=xr[p];y_top=yt[p];y_bot=yb[p];
@<Look for overlaps in the successors of node |q|@>;
@<Look for overlaps in node |q| and its predecessors@>;
return false;
} 

@ @<Look for overlaps in the successors of node |q|@>=
y_thresh=y_bot+max_height;r=next[q];
while (yy[r] < y_thresh) 
  {@+if (y_bot > yt[r]) if (x_left < xr[r]) 
   if (x_right > xl[r]) if (y_top < yb[r]) 
    {@+return true;
    } 
  r=next[r];
  } 
  
@ @<Look for overlaps in node |q| and its predecessors@>=
y_thresh=y_top-max_depth;r=q;
while (yy[r] > y_thresh) 
  {@+if (y_bot > yt[r]) if (x_left < xr[r]) 
   if (x_right > xl[r]) if (y_top < yb[r]) 
    {@+return true;
    } 
  r=prev[r];
  } 

@ Nodes that represent dots instead of labels satisfy the following
constraints:
$$\vcenter{\halign{#\hfil&\quad#\hfil\cr
|info[p] < 0;|&|p >= first_dot|;\cr
|xl[p]==xx[p]-dot_width|,&|xr[p]==xx[p]+dot_width|;\cr
|yt[p]==yy[p]-dot_height|,&|yb[p]==yy[p]+dot_height|.\cr}}$$

The |nearest_dot| subroutine finds a node whose reference point is as
close as possible to a given position, ignoring nodes that are too close.
More precisely, the ``nearest'' node
minimizes$$d(q,p)=\max\bigl(\vert |xx|[q]-|xx|[p]\vert,
  \vert |yy|[q]-|yy|[p]\vert\bigr)$$ over all nodes~|q|
with |d(q, p) >= d0|. We call the subroutine |nearest_dot| because it is used only
when the doubly linked list contains nothing but dots.

The routine also sets the global variable |twin| to |true|, if there is a
node |q!=p| with |d(q, p) < d0|.

@ @<Glob...@>=
node_pointer @!first_dot; /*the node address where dots begin*/ 
bool @!twin; /*is there a nearer dot than the ``nearest'' dot?*/ 

@ If there is no nearest dot, the value |null| is returned;
otherwise a pointer to the nearest dot is returned.

@p node_pointer nearest_dot(node_pointer @!p, scaled @!d0)
{@+node_pointer @!best_q; /*value to return*/ 
scaled @!d_min, @!d; /*distances*/ 
twin=false;best_q=0;d_min=02000000000;
@<Search for the nearest dot in nodes following |p|@>;
@<Search for the nearest dot in nodes preceding |p|@>;
return best_q;
} 

@ @<Search for the nearest dot in nodes following |p|@>=
q=next[p];
while (yy[q] < yy[p]+d_min) 
  {@+d=abs(xx[q]-xx[p]);
  if (d < yy[q]-yy[p]) d=yy[q]-yy[p];
  if (d < d0) twin=true;
  else if (d < d_min) 
    {@+d_min=d;best_q=q;
    } 
  q=next[q];
  } 

@ @<Search for the nearest dot in nodes preceding |p|@>=
q=prev[p];
while (yy[q] > yy[p]-d_min) 
  {@+d=abs(xx[q]-xx[p]);
  if (d < yy[p]-yy[q]) d=yy[p]-yy[q];
  if (d < d0) twin=true;
  else if (d < d_min) 
    {@+d_min=d;best_q=q;
    } 
  q=prev[q];
  } 

@*Doing the labels.
Each ``character'' in the \.{GF} file is preceded by a number of special
commands that define labels, titles, rules, etc. We store these away,
to be considered later when the |boc| command appears. The |boc|
command establishes the size information by which labels and rules
can be positioned, so we spew out the label information as soon as
we see the |boc|. The gray pixels will be typeset after all the labels
for a particular character have been finished.

@ Here is the part of \.{GFtoDVI} that stores information preceding a~|boc|.
It comes into play when |cur_gf| is between |xxx1| and~|no_op|, inclusive.

@d font_change(X)	if (fonts_not_loaded) 
    {@+X;} 
  else print_nl("(Tardy font change will be ignored (byte %d)!)",
@.Tardy font change...@>
    cur_loc)

@<Process a no-op command@>=
{@+k=interpret_xxx();
switch (k) {
case no_operation: do_nothing;@+break;
case title_font: case label_font: case gray_font: case slant_font: font_change(font_name[k]=cur_string;
  font_area[k]=null_string;font_at[k]=0;init_str_ptr=str_ptr)@;@+break;
case title_font+area_code: case label_font+area_code: case gray_font+area_code: 
  case slant_font+area_code: @|
  font_change(font_area[k-area_code]=cur_string;init_str_ptr=str_ptr)@;@+break;
case title_font+at_code: case label_font+at_code: case gray_font+at_code: 
  case slant_font+at_code: @|
  font_change(font_at[k-at_code]=get_yyy();init_str_ptr=str_ptr)@;@+break;
case rule_thickness_code: rule_thickness=get_yyy();@+break;
case rule_code: @<Store a rule@>@;@+break;
case offset_code: @<Override the offsets@>@;@+break;
case x_offset_code: x_offset=get_yyy();@+break;
case y_offset_code: y_offset=get_yyy();@+break;
case title_code: @<Store a title@>@;@+break;
case null_string: @<Store a label@>;
}  /*there are no other cases*/ 
} 

@ The following quantities are cleared just before reading the
\.{GF} commands pertaining to a character.

@<Glob...@>=
scaled @!rule_thickness; /*the current rule thickness
  (zero means use the default)*/ 
scaled @!offset_x, @!offset_y; /*the current offsets for images*/ 
scaled @!x_offset, @!y_offset; /*the current offsets for labels*/ 
scaled @!pre_min_x, @!pre_max_x, @!pre_min_y, @!pre_max_y;
   /*extreme values of coordinates preceding a character, in \MF\ pixels*/ 

@ @<Initialize variables for the next character@>=
rule_thickness=0;
offset_x=0;offset_y=0;x_offset=0;y_offset=0;
pre_min_x=02000000000;pre_max_x=-02000000000;
pre_min_y=02000000000;pre_max_y=-02000000000;

@ @<Override the offsets@>=
{@+offset_x=get_yyy();offset_y=get_yyy();
} 

@ Rules that will need to be drawn are kept in a linked list accessible
via |rule_ptr|, in last-in-first-out order.  The nodes of this list will
never get into the doubly linked list, and indeed these nodes use different
field conventions entirely (because rules may be slanted).

@d x0	xl /*starting |x| coordinate of a stored rule*/ 
@d y0	yt /*starting |y| coordinate (in scaled \MF\ pixels)*/ 
@d x1	xr /*ending |x| coordinate of a stored rule*/ 
@d y1	yb /*ending |y| coordinate of a stored rule*/ 
@d rule_size	xx /*thickness of a stored rule, in scaled points*/ 

@<Glob...@>=
node_pointer @!rule_ptr; /*top of the stack of remembered rules*/ 

@ @<Store a rule@>=
{@+p=get_avail();next[p]=rule_ptr;rule_ptr=p;@/
x0[p]=get_yyy();y0[p]=get_yyy();x1[p]=get_yyy();y1[p]=get_yyy();
if (x0[p] < pre_min_x) pre_min_x=x0[p];
if (x0[p] > pre_max_x) pre_max_x=x0[p];
if (y0[p] < pre_min_y) pre_min_y=y0[p];
if (y0[p] > pre_max_y) pre_max_y=y0[p];
if (x1[p] < pre_min_x) pre_min_x=x1[p];
if (x1[p] > pre_max_x) pre_max_x=x1[p];
if (y1[p] < pre_min_y) pre_min_y=y1[p];
if (y1[p] > pre_max_y) pre_max_y=y1[p];
rule_size[p]=rule_thickness;
} 

@ Titles and labels are, likewise, stored temporarily in singly linked lists.
In this case the lists are first-in-first-out.
Variables |title_tail| and |label_tail| point to the most recently inserted
title or label; variables |title_head| and |label_head|
point to the beginning of the list. (A standard coding trick is used
for |label_head|, which is kept in |next[end_of_list]|; we have
|label_tail==end_of_list| when the list is empty.)

The |prev| field in nodes of the temporary label list specifies the
type of label, so we call it |lab_typ|.

@d lab_typ	prev /*the type of a stored label (|'/'dotdot.'8'|)*/ 
@d label_head	next[end_of_list]

@<Glob...@>=
node_pointer @!label_tail; /*tail of the queue of remembered labels*/ 
node_pointer @!title_head, @!title_tail; /*head and tail of the queue for titles*/ 

@ We must start the lists out empty.

@<Initialize variables for the next char...@>=
rule_ptr=null;
title_head=null;title_tail=null;label_head=null;label_tail=end_of_list;
first_dot=max_labels;

@ @<Store a title@>=
{@+p=get_avail();info[p]=cur_string;
if (title_head==null) title_head=p;
else next[title_tail]=p;
title_tail=p;
} 

@ We store the coordinates of each label in units of \MF\ pixels; they
will be converted to \.{DVI} coordinates later.

@<Store a label@>=
if ((label_type < '/')||(label_type > '8')) 
  print_nl("Bad label type precedes byte %d!", cur_loc)@;
@.Bad label type...@>
else{@+p=get_avail();next[label_tail]=p;label_tail=p;@/
  lab_typ[p]=label_type;info[p]=cur_string;@/
  xx[p]=get_yyy();yy[p]=get_yyy();
  if (xx[p] < pre_min_x) pre_min_x=xx[p];
  if (xx[p] > pre_max_x) pre_max_x=xx[p];
  if (yy[p] < pre_min_y) pre_min_y=yy[p];
  if (yy[p] > pre_max_y) pre_max_y=yy[p];
  } 

@ The process of ferreting everything away comes to an abrupt halt
when a |boc| command is sensed. The following steps are performed
at such times:

@<Process a character@>=
{@+check_fonts;
@<Finish reading the parameters of the |boc|@>;
@<Get ready to convert \MF\ coordinates to \.{DVI} coordinates@>;
@<Output the |bop| and the title line@>;
print("[%d", total_pages);update_terminal; /*print a progress report*/
@<Output all rules for the current character@>;
@<Output all labels for the current character@>;
do_pixels();
dvi_out(eop); /*finish the page*/ 
@<Adjust the maximum page width@>;
print("]");update_terminal;
} 

@ @<Finish reading the parameters of the |boc|@>=
if (cur_gf==boc) 
  {@+ext=signed_quad(); /*read the character code*/ 
  char_code=ext%256;
  if (char_code < 0) char_code=char_code+256;
  ext=(ext-char_code)/256;
  k=signed_quad(); /*read and ignore the prev pointer*/ 
  min_x=signed_quad(); /*read the minimum $x$ coordinate*/ 
  max_x=signed_quad(); /*read the maximum $x$ coordinate*/ 
  min_y=signed_quad(); /*read the minimum $y$ coordinate*/ 
  max_y=signed_quad(); /*read the maximum $y$ coordinate*/ 
  } 
else{@+ext=0;char_code=get_byte(); /*|cur_gf==boc1|*/ 
  min_x=get_byte();max_x=get_byte();min_x=max_x-min_x;@/
  min_y=get_byte();max_y=get_byte();min_y=max_y-min_y;
  } 
if (max_x-min_x > widest_row) abort("Character too wide!")
@.Character too wide@>

@ @<Glob...@>=
int @!char_code, @!ext; /*the current character code and extension*/ 
int @!min_x, @!max_x, @!min_y, @!max_y; /*character boundaries, in pixels*/ 
int @!x, @!y; /*current painting position, in pixels*/ 
int @!z; /*initial painting position in row, relative to |min_x|*/ 

@ \MF\ coordinates $(x,y)$ are converted to \.{DVI} coordinates by the
following routine. Real values |x_ratio|, |y_ratio|, and |slant_ratio|
will have been calculated based on the gray font; |scaled| values
|delta_x| and |delta_y| will have been computed so that, in the absence
of slanting and offsets, the \MF\ coordinates |(min_x, max_y+1)| will correspond
to the \.{DVI} coordinates $(0,50\,\rm pt)$.

@p void convert(scaled @!x, scaled @!y)
{@+x=x+x_offset;y=y+y_offset;
dvi_y=-round(y_ratio*y)+delta_y;
dvi_x=round(x_ratio*x+slant_ratio*y)+delta_x;
} 

@ @<Glob...@>=
double @!x_ratio, @!y_ratio, @!slant_ratio; /*conversion factors*/ 
double @!unsc_x_ratio, @!unsc_y_ratio, @!unsc_slant_ratio;
   /*ditto, times |unity|*/ 
double @!fudge_factor; /*unconversion factor*/ 
scaled @!delta_x, @!delta_y; /*magic constants used by |convert|*/ 
scaled @!dvi_x, @!dvi_y; /*outputs of |convert|, in scaled points*/ 
scaled @!over_col; /*overflow labels start here*/ 
scaled @!page_height, page_width; /*size of the current page*/ 

@ @<Initialize global variables that depend on the font data@>=
i=char_info(gray_font)(1);
if (!char_exists(i)) abort("Missing pixel char!");
@.Missing pixel char@>
unsc_x_ratio=char_width(gray_font)(i);
x_ratio=unsc_x_ratio/(double)unity;
unsc_y_ratio=char_height(gray_font)(height_depth(i));
y_ratio=unsc_y_ratio/(double)unity;
unsc_slant_ratio=slant(gray_font)*y_ratio;
slant_ratio=unsc_slant_ratio/(double)unity;
if (x_ratio*y_ratio==0) abort("Vanishing pixel size!");
@.Vanishing pixel size@>
fudge_factor=(slant_ratio/(double)x_ratio)/(double)y_ratio;

@ @<Get ready to convert...@>=
if (pre_min_x < min_x*unity) offset_x=offset_x+min_x*unity-pre_min_x;
if (pre_max_y > max_y*unity) offset_y=offset_y+max_y*unity-pre_max_y;
if (pre_max_x > max_x*unity) pre_max_x=pre_max_x/unity;
else pre_max_x=max_x;
if (pre_min_y < min_y*unity) pre_min_y=pre_min_y/unity;
else pre_min_y=min_y;
delta_y=round(unsc_y_ratio*(max_y+1)-y_ratio*offset_y)+3276800;
delta_x=round(x_ratio*offset_x-unsc_x_ratio*min_x);
if (slant_ratio >= 0) 
  over_col=round(unsc_x_ratio*pre_max_x+unsc_slant_ratio*max_y);
else over_col=round(unsc_x_ratio*pre_max_x+unsc_slant_ratio*min_y);
over_col=over_col+delta_x+10000000;
page_height=round(unsc_y_ratio*(max_y+1-pre_min_y))+3276800-offset_y;
if (page_height > max_v) max_v=page_height;
page_width=over_col-10000000

@ The |dvi_goto| subroutine outputs bytes to the \.{DVI} file that
will initiate typesetting at given \.{DVI} coordinates, assuming that
the current position of the \.{DVI} reader is $(0,0)$. This subroutine
begins by outputting a |push| command; therefore, a |pop| command should
be given later. That |pop| will restore the \.{DVI} position to $(0,0)$.

@p void dvi_goto(scaled @!x, scaled @!y)
{@+dvi_out(push);
if (x!=0) 
  {@+dvi_out(right4);dvi_four(x);
  } 
if (y!=0) 
  {@+dvi_out(down4);dvi_four(y);
  } 
} 

@ @<Output the |bop| and the title line@>=
dvi_out(bop);incr(total_pages);dvi_four(total_pages);
dvi_four(char_code);dvi_four(ext);
for (k=3; k<=9; k++) dvi_four(0);
dvi_four(last_bop);last_bop=dvi_offset+dvi_ptr-45;@/
dvi_goto(0, 655360); /*the top baseline is 10\thinspace pt down*/ 
if (use_logo) 
  {@+select_font(logo_font);hbox(small_logo, logo_font, true);
  } 
select_font(title_font);hbox(time_stamp, title_font, true);@/
hbox(page_header, title_font, true);dvi_scaled(total_pages*65536.0);@/
if ((char_code!=0)||(ext!=0)) 
  {@+hbox(char_header, title_font, true);dvi_scaled(char_code*65536.0);
  if (ext!=0) 
    {@+hbox(ext_header, title_font, true);dvi_scaled(ext*65536.0);
    } 
  } 
if (title_head!=null) 
  {@+next[title_tail]=null;
  @/do@+{hbox(left_quotes, title_font, true);
  hbox(info[title_head], title_font, true);
  hbox(right_quotes, title_font, true);
  title_head=next[title_head];
  }@+ while (!(title_head==null));
  } 
dvi_out(pop)

@ @d tol	6554 /*one tenth of a point, in \.{DVI} coordinates*/ 

@<Output all rules for the current character@>=
if (rule_slant!=0) select_font(slant_font);
while (rule_ptr!=null) 
  {@+p=rule_ptr;rule_ptr=next[p];@/
  if (rule_size[p]==0) rule_size[p]=gray_rule_thickness;
  if (rule_size[p] > 0) 
    {@+convert(x0[p], y0[p]);temp_x=dvi_x;temp_y=dvi_y;
    convert(x1[p], y1[p]);
    if (abs(temp_x-dvi_x) < tol) @<Output a vertical rule@>@;
    else if (abs(temp_y-dvi_y) < tol) @<Output a horizontal rule@>@;
    else@<Try to output a diagonal rule@>;
    } 
  } 

@ @<Glob...@>=
scaled @!gray_rule_thickness; /*thickness of rules, according to the gray font*/ 
scaled @!temp_x, @!temp_y; /*temporary registers for intermediate calculations*/ 

@ @<Initialize glob...@>=
gray_rule_thickness=default_rule_thickness(gray_font);
if (gray_rule_thickness==0) gray_rule_thickness=26214; /*0.4\thinspace pt*/ 

@ @<Output a vertical rule@>=
{@+if (temp_y > dvi_y) 
  {@+k=temp_y;temp_y=dvi_y;dvi_y=k;
  } 
dvi_goto(dvi_x-(rule_size[p]/2), dvi_y);
dvi_out(put_rule);dvi_four(dvi_y-temp_y);dvi_four(rule_size[p]);
dvi_out(pop);
} 

@ @<Output a horizontal rule@>=
{@+if (temp_x < dvi_x) 
  {@+k=temp_x;temp_x=dvi_x;dvi_x=k;
  } 
dvi_goto(dvi_x, dvi_y+(rule_size[p]/2));
dvi_out(put_rule);dvi_four(rule_size[p]);dvi_four(temp_x-dvi_x);
dvi_out(pop);
} 

@ @<Try to output a diagonal rule@>=
if ((rule_slant==0)||@|
 (abs(temp_x+rule_slant*(temp_y-dvi_y)-dvi_x) > rule_size[p])) 
  slant_complaint((dvi_x-temp_x)/(double)(temp_y-dvi_y));
else{@+if (temp_y > dvi_y) 
    {@+k=temp_y;temp_y=dvi_y;dvi_y=k;@/
    k=temp_x;temp_x=dvi_x;dvi_x=k;
    } 
  m=round((dvi_y-temp_y)/(double)slant_unit);
  if (m > 0) 
    {@+dvi_goto(dvi_x, dvi_y);
    q=((m-1)/slant_n)+1;k=m/q;
    p=m%q;q=q-p;
    @<Vertically typeset |q| copies of character |k|@>;
    @<Vertically typeset |p| copies of character |k+1|@>;
    dvi_out(pop);
    } 
  } 

@ @<Vertically typeset |q| copies of character |k|@>=
typeset(k);dy=round(k*slant_unit);dvi_out(z4);dvi_four(-dy);
while (q > 1) 
  {@+typeset(k);dvi_out(z0);decr(q);
  } 

@ @<Vertically typeset |p| copies of character |k+1|@>=
if (p > 0) 
  {@+incr(k);typeset(k);
  dy=round(k*slant_unit);dvi_out(z4);dvi_four(-dy);
  while (p > 1) 
    {@+typeset(k);dvi_out(z0);decr(p);
    } 
  } 

@ Now we come to a more interesting part of the computation, where we
go through the stored labels and try to fit them in the illustration for
the current character, together with their associated dots.

It would simplify font-switching slightly if we were to typeset the labels
first, but we find it desirable to typeset the dots first and then turn to the
labels. This procedure makes it possible for us to allow the dots to
overlap each other without allowing the labels to overlap. After the
dots are in place, we typeset all prescribed labels, that is, labels with a
|lab_typ| of |'1'dotdot'8'|; these, too, are allowed to overlap the dots and
each other.

@<Output all labels for the current character@>=
overflow_line=1;
if (label_head!=null) 
  {@+next[label_tail]=null;select_font(gray_font);
  @<Output all dots@>;
  @<Find nearest dots, to help in label positioning@>;
  select_font(label_font);
  @<Output all prescribed labels@>;
  @<Output all attachable labels@>;
  @<Output all overflow labels@>;
  } 

@ @<Glob...@>=
int @!overflow_line; /*the number of labels that didn't fit, plus~1*/ 

@ A label that appears above its dot is considered to occupy a
rectangle of height~$h+\Delta$, depth~$d$, and width~$w+2\Delta$, where
$(h,w,d)$ are the height, width, and depth of the label computed by |hbox|,
and $\Delta$ is an additional amount of blank space that keeps labels from
coming too close to each other. (\.{GFtoDVI} arbitrarily defines $\Delta$
to be one half the width of a space in the label font.) This label is
centered over its dot, with its baseline $d+h'$ above the center of the dot;
here $h'=|dot_height|$ is the height of character~0 in the gray font.

Similarly, a label that appears below its dot is considered to occupy
a rectangle of height~$h$, depth~$d+\Delta$, and width~$w+2\Delta$; the
baseline is $h+h'$ below the center of the dot.

A label at the right of its dot is considered to occupy a rectangle of
height~$h+\Delta$, depth~$d+\Delta$, and width~$w+\Delta$. Its
reference point can be found by starting at the center of the dot and
moving right $w'=|dot_width|$ (i.e., the width of character~0 in the
gray font), then moving down by half the x-height of the label font.
A label at the left of its dot is similar.

A dot is considered to occupy a rectangle of height $2h'$ and width~$2w'$,
centered on the dot.

When the label type is |'1'| or more, the labels
are put into the doubly linked list unconditionally.
 Otherwise they are put into the list
only if we can find a way to fit them in without
overlapping any previously inserted rectangles.

@<Glob...@>=
scaled @!delta; /*extra padding to keep labels from being too close*/ 
scaled @!half_x_height; /*amount to drop baseline of label below the dot center*/ 
scaled @!thrice_x_height; /*baseline separation for overflow labels*/ 
scaled @!dot_width, @!dot_height; /*$w'$ and $h'$ in the discussion above*/ 

@ @<Initialize global variables that depend on the font data@>=
i=char_info(gray_font)(0);
if (!char_exists(i)) abort("Missing dot char!");
@.Missing dot char@>
dot_width=char_width(gray_font)(i);
dot_height=char_height(gray_font)(height_depth(i));
delta=space(label_font)/2;
thrice_x_height=3*x_height(label_font);
half_x_height=thrice_x_height/6;

@ Here is a subroutine that computes the rectangle boundaries
|xl[p]|, |xr[p]|, |yt[p]|, |yb[p]|, and the reference point coordinates
|xx[p]|,~|yy[p]|, for a label that is to be placed above a dot.
The coordinates of the dot's center are assumed given in |dvi_x|
and |dvi_y|; the |hbox| subroutine is assumed to have
already computed the height, width, and depth of the label box.

@p void top_coords(node_pointer @!p)
{@+xx[p]=dvi_x-(box_width/2);xl[p]=xx[p]-delta;
xr[p]=xx[p]+box_width+delta;@/
yb[p]=dvi_y-dot_height;yy[p]=yb[p]-box_depth;
yt[p]=yy[p]-box_height-delta;
} 

@ The other three label positions are handled by similar routines.

@p void bot_coords(node_pointer @!p)
{@+xx[p]=dvi_x-(box_width/2);xl[p]=xx[p]-delta;
xr[p]=xx[p]+box_width+delta;@/
yt[p]=dvi_y+dot_height;yy[p]=yt[p]+box_height;
yb[p]=yy[p]+box_depth+delta;
} 
@#
void right_coords(node_pointer @!p)
{@+xl[p]=dvi_x+dot_width;xx[p]=xl[p];xr[p]=xx[p]+box_width+delta;@/
yy[p]=dvi_y+half_x_height;yb[p]=yy[p]+box_depth+delta;
yt[p]=yy[p]-box_height-delta;
} 
@#
void left_coords(node_pointer @!p)
{@+xr[p]=dvi_x-dot_width;xx[p]=xr[p]-box_width;xl[p]=xx[p]-delta;@/
yy[p]=dvi_y+half_x_height;yb[p]=yy[p]+box_depth+delta;
yt[p]=yy[p]-box_height-delta;
} 

@ @<Output all dots@>=
p=label_head;first_dot=max_node+1;
while (p!=null) 
  {@+convert(xx[p], yy[p]);xx[p]=dvi_x;yy[p]=dvi_y;
  if (lab_typ[p] < '5') 
    @<Enter a dot for label |p| in the rectangle list, and typeset the dot@>;
  p=next[p];
  } 

@ We plant links between dots and their labels by using (or abusing) the
|xl| and |info| fields, which aren't needed for their normal purposes.

@d dot_for_label	xl
@d label_for_dot	info

@<Enter a dot...@>=
{@+q=get_avail();dot_for_label[p]=q;label_for_dot[q]=p;@/
xx[q]=dvi_x;xl[q]=dvi_x-dot_width;xr[q]=dvi_x+dot_width;@/
yy[q]=dvi_y;yt[q]=dvi_y-dot_height;yb[q]=dvi_y+dot_height;@/
node_ins(q, 0);@/
dvi_goto(xx[q], yy[q]);dvi_out(0);dvi_out(pop);
} 

@ Prescribed labels are now taken out of the singly linked list and
inserted into the doubly linked list.

@<Output all prescribed labels@>=
q=end_of_list; /*|label_head==next[q]|*/ 
while (next[q]!=null) 
  {@+p=next[q];
  if (lab_typ[p] > '0') 
    {@+next[q]=next[p];
    @<Enter a prescribed label for node |p| into the rectangle list, and typeset it@>;
    } 
  else q=next[q];
  } 

@ @<Enter a prescr...@>=
{@+hbox(info[p], label_font, false); /*Compute the size of this label*/ 
dvi_x=xx[p];dvi_y=yy[p];
if (lab_typ[p] < '5') r=dot_for_label[p];@+else r=0;
switch (lab_typ[p]) {
case '1': case '5': top_coords(p);@+break;
case '2': case '6': left_coords(p);@+break;
case '3': case '7': right_coords(p);@+break;
case '4': case '8': bot_coords(p);
}  /*no other cases are possible*/ 
node_ins(p, r);@/
dvi_goto(xx[p], yy[p]);hbox(info[p], label_font, true);dvi_out(pop);
} 

@ \.{GFtoDVI}'s algorithm for positioning the ``floating'' labels
was devised by Arthur~L. Samuel.
@^Samuel, Arthur Lee@>
It tries to place labels in a priority order, based on the position of
the nearest dot to a given dot. If that dot, for example, lies in the first
octant (i.e., east to northeast of the given dot), the given label will
be put into the west slot unless that slot is already blocked; then the
south slot will be tried, etc.

First we need to compute the octants. We also note if two or more dots
are nearly coincident, since Samuel's algorithm modifies the priority
order on that case. The information is temporarily recorded in the |xr| array.

@d octant	xr /*octant code for nearest dot, plus 8 for coincident dots*/ 

@<Find nearest dots, to help in label positioning@>=
p=label_head;
while (p!=null) 
  {@+if (lab_typ[p] <= '0') 
    @<Compute the octant code for floating label |p|@>;
  p=next[p];
  } 

@ There's a sneaky way to identify octant numbers, represented by the
code shown here. (Remember that |y|~coordinates increase downward
in the \.{DVI} convention.)

@d first_octant	0
@d second_octant	1
@d third_octant	2
@d fourth_octant	3
@d fifth_octant	7
@d sixth_octant	6
@d seventh_octant	5
@d eighth_octant	4

@<Compute the octant code for floating label |p|@>=
{@+r=dot_for_label[p];q=nearest_dot(r, 10);
if (twin) octant[p]=8;@+else octant[p]=0;
if (q!=null) 
  {@+dx=xx[q]-xx[r];dy=yy[q]-yy[r];
  if (dy > 0) octant[p]=octant[p]+4;
  if (dx < 0) incr(octant[p]);
  if (dy > dx) incr(octant[p]);
  if (-dy > dx) incr(octant[p]);
  } 
} 

@ A procedure called |place_label| will try to place the remaining
labels in turn. If it fails, we ``disconnect'' the dot from this
label so that an unlabeled dot will not appear as a reference in the
overflow column.

@<Output all attachable labels@>=
q=end_of_list; /*now |next[q]==label_head|*/ 
while (next[q]!=null) 
  {@+p=next[q];r=next[p];s=dot_for_label[p];
  if (place_label(p)) next[q]=r;
  else{@+label_for_dot[s]=null; /*disconnect the dot*/ 
    if (lab_typ[p]=='/') next[q]=r; /*remove label from list*/ 
    else q=p; /*retain label in list for the overflow column*/ 
    } 
  } 

@ Here is the |place_label| routine, which uses the previously computed
|octant| information as a heuristic. If the label can be placed, it
is inserted into the rectangle list and typeset.

@p bool place_label(node_pointer @!p)
{@+
uint8_t @!oct; /*octant code*/ 
node_pointer @!dfl; /*saved value of |dot_for_label[p]|*/ 
hbox(info[p], label_font, false); /*Compute the size of this label*/ 
dvi_x=xx[p];dvi_y=yy[p];
@<Find non-overlapping coordinates, if possible, and |goto| found; otherwise set |place_label:=false|
and |return|@>;
found: node_ins(p, dfl);@/
dvi_goto(xx[p], yy[p]);hbox(info[p], label_font, true);dvi_out(pop);
return true;
} 

@ @<Find non-overlapping coordinates, if possible...@>=
dfl=dot_for_label[p];oct=octant[p];
@<Try the first choice for label direction@>;
@<Try the second choice for label direction@>;
@<Try the third choice for label direction@>;
@<Try the fourth choice for label direction@>;
xx[p]=dvi_x;yy[p]=dvi_y;dot_for_label[p]=dfl; /*no luck; restore the coordinates*/ 
return false;
@ @<Try the first choice for label direction@>=
switch (oct) {
case first_octant: case eighth_octant: case second_octant+8: case seventh_octant+8: left_coords(p);@+break;
case second_octant: case third_octant: case first_octant+8: case fourth_octant+8: bot_coords(p);@+break;
case fourth_octant: case fifth_octant: case third_octant+8: case sixth_octant+8: right_coords(p);@+break;
case sixth_octant: case seventh_octant: case fifth_octant+8: case eighth_octant+8: top_coords(p);
} 
if (!overlap(p, dfl)) goto found

@ @<Try the second choice for label direction@>=
switch (oct) {
case first_octant: case fourth_octant: case fifth_octant+8: case eighth_octant+8: bot_coords(p);@+break;
case second_octant: case seventh_octant: case third_octant+8: case sixth_octant+8: left_coords(p);@+break;
case third_octant: case sixth_octant: case second_octant+8: case seventh_octant+8: right_coords(p);@+break;
case fifth_octant: case eighth_octant: case first_octant+8: case fourth_octant+8: top_coords(p);
} 
if (!overlap(p, dfl)) goto found

@ @<Try the third choice for label direction@>=
switch (oct) {
case first_octant: case fourth_octant: case sixth_octant+8: case seventh_octant+8: top_coords(p);@+break;
case second_octant: case seventh_octant: case fourth_octant+8: case fifth_octant+8: right_coords(p);@+break;
case third_octant: case sixth_octant: case first_octant+8: case eighth_octant+8: left_coords(p);@+break;
case fifth_octant: case eighth_octant: case second_octant+8: case third_octant+8: bot_coords(p);
} 
if (!overlap(p, dfl)) goto found

@ @<Try the fourth choice for label direction@>=
switch (oct) {
case first_octant: case eighth_octant: case first_octant+8: case eighth_octant+8: right_coords(p);@+break;
case second_octant: case third_octant: case second_octant+8: case third_octant+8: top_coords(p);@+break;
case fourth_octant: case fifth_octant: case fourth_octant+8: case fifth_octant+8: left_coords(p);@+break;
case sixth_octant: case seventh_octant: case sixth_octant+8: case seventh_octant+8: bot_coords(p);
} 
if (!overlap(p, dfl)) goto found

@ @<Output all overflow labels@>=
@<Remove all rectangles from list, except for dots that have labels@>;
p=label_head;
while (p!=null) 
  {@+@<Typeset an overflow label for |p|@>;
  p=next[p];
  } 

@ When we remove a dot that couldn't be labeled, we set its |next| field
to the preceding node that survives, so that we can use the |nearest_dot|
routine later. (This is a bit of a kludge.)

@<Remove all rectangles from list, except for dots that have labels@>=
p=next[0];
while (p!=end_of_list) 
  {@+q=next[p];
  if ((p < first_dot)||(label_for_dot[p]==null)) 
    {@+r=prev[p];next[r]=q;prev[q]=r;next[p]=r;
    } 
  p=q;
  } 

@ Now we have to insert |p| into the list temporarily, because of the
way |nearest_dot| works.

@<Typeset an overflow label for |p|@>=
{@+r=next[dot_for_label[p]];s=next[r];t=next[p];
next[p]=s;prev[s]=p;next[r]=p;prev[p]=r;@/
q=nearest_dot(p, 0);@/
next[r]=s;prev[s]=r;next[p]=t; /*remove |p| again*/ 
incr(overflow_line);
dvi_goto(over_col, overflow_line*thrice_x_height+655360);
hbox(info[p], label_font, true);
if (q!=null) 
  {@+hbox(equals_sign, label_font, true);
  hbox(info[label_for_dot[q]], label_font, true);
  hbox(plus_sign, label_font, true);
  dvi_scaled((xx[p]-xx[q])/(double)x_ratio+(yy[p]-yy[q])*fudge_factor);
  dvi_out(',');
  dvi_scaled((yy[q]-yy[p])/(double)y_ratio);
  dvi_out(')');
  } 
dvi_out(pop);
} 

@ @<Adjust the maximum page width@>=
if (overflow_line > 1) page_width=over_col+10000000;
   /*overflow labels are estimated to occupy $10^7\,$sp*/ 
if (page_width > max_h) max_h=page_width

@*Doing the pixels.
The most interesting part of \.{GFtoDVI} is the way it makes use of a gray
font to typeset the pixels of a character. In fact, the author must admit having
great fun devising the algorithms below. Perhaps the reader will also
enjoy reading them.

The basic idea will be to use an array of 12-bit integers to represent the next
twelve rows that need to be typeset. The binary expansions of these integers,
reading from least significant bit to most significant bit, will represent
pixels from top to bottom.

@ We have already used such a binary representation in the tables
|c[1 dotdot 120]| and |d[1 dotdot 120]| of bit patterns and lengths that are potentially
present in a gray font; we shall now use those tables to compute
an auxiliary array |b[0 dotdot 4095]|. Given a 12-bit number~$v$, the gray-font
character appropriate to $v$'s binary pattern will be~|b[v]|. If no
character should be typeset for this pattern in the current row,
|b[v]| will be~0.

The array |b| can have many different configurations, depending on how
many characters are actually present in the gray font. But
it's not difficult to compute |b| by going through the existing characters
in increasing order and marking all patterns~$x$ to which they apply.

@<Initialize glob...@>=
for (k=0; k<=4095; k++) b[k]=0;
for (k=font_bc[gray_font]; k<=font_ec[gray_font]; k++) 
 if (k >= 1) if (k <= 120) 
  if (char_exists(char_info(gray_font)(k))) 
  {@+v=c[k];
  @/do@+{b[v]=k;v=v+d[k];
  }@+ while (!(v > 4095));
  } 

@ We also compute an auxiliary array |rho[0 dotdot 4095]| such that $\\{rho}[v]=2^j$
when |v| is an odd multiple of~$2^j$; we also set $\\{rho}[0]=2^{12}$.

@<Initialize g...@>=
for (j=0; j<=11; j++) 
  {@+k=two_to_the[j];v=k;
  @/do@+{rho[v]=k;v=v+k+k;
  }@+ while (!(v > 4095));
  } 
rho[0]=4096;

@ @<Glob...@>=
uint8_t @!b[4096]; /*largest existing character for a given pattern*/ 
uint16_t @!rho[4096]; /*the ``ruler function''*/ 

@ But how will we use these tables? Let's imagine that the \.{DVI} file
already contains instructions that have selected the gray font and moved
to the proper horizontal coordinate for the row that we wish to process next.
Let's suppose that 12-bit patterns have been set up in array~|a|, and that
the global variables |starting_col| and |finishing_col| are known such
that |a[j]| is zero unless |starting_col <= j <= finishing_col|. Here's what
we can do, assuming that appropriate local variables and labels have
been declared:

@<Typeset the pixels of the current row@>=
j=starting_col;
loop@+{@+while ((j <= finishing_col)&&(b[a[j]]==0)) incr(j);
  if (j > finishing_col) goto done;
  dvi_out(push);@<Move to column |j| in the \.{DVI} output@>;
  @/do@+{v=b[a[j]];a[j]=a[j]-c[v];
  k=j;incr(j);
  while (b[a[j]]==v) 
    {@+a[j]=a[j]-c[v];incr(j);
    } 
  k=j-k;@<Output the equivalent of |k| copies of character |v|@>;
  }@+ while (!(b[a[j]]==0));
  dvi_out(pop);
  } 
done: 

@ @<Move to column |j| in the \.{DVI} output@>=
dvi_out(right4);
dvi_four(round(unsc_x_ratio*j+unsc_slant_ratio*y)+delta_x)

@ The doubling-up property of gray font character lists is utilized here.

@<Output the equivalent of |k| copies of character |v|@>=
reswitch: if (k==1) typeset(v);
else{@+i=char_info(gray_font)(v);
  if (char_tag(i)==list_tag)  /*|v| has a successor*/ 
    {@+if (odd(k)) typeset(v);
    k=k/2;v=qo(rem_byte(i));goto reswitch;
    } 
  else@/do@+{typeset(v);decr(k);
    }@+ while (!(k==0));
  } 

@ @<Glob...@>=
uint16_t @!a[widest_row+1]; /*bit patterns for twelve rows*/ 

@ In order to use the approach above, we need to be able to initialize
array~|a|, and we need to be able to keep it up to date as new rows
scroll by. A moment's thought about the problem reveals that we will either
have to read an entire character from the \.{GF} file into memory,
or we'll need to adopt a coroutine-like approach: A single \\{skip}
command in the \.{GF} file might need to be processed in pieces, since
it might generate more rows of zeroes than we are ready to absorb
all at once into~|a|.

The coroutine method actually turns out to be quite simple, so we shall
introduce a global variable |blank_rows|, which tells how many rows of
blanks should be generated before we read the \.{GF} instructions
for another row.

@<Glob...@>=
int @!blank_rows;
   /*rows of blanks carried over from a previous \.{GF} command*/ 

@ Initialization and updating of~|a| can now be handled as follows,
if we introduce another variable~|l| that is set initially to~1:

@<Add more rows to |a|, until 12-bit entries are obtained@>=
@/do@+{@<Put the bits for the next row, times |l|, into |a|@>;
l=l+l;decr(y);
}@+ while (!(l==4096));

@ As before, |cur_gf| will contain the first \.{GF} command that has
not yet been interpreted.

@<Put the bits...@>=
if (blank_rows > 0) decr(blank_rows);
else if (cur_gf!=eoc) 
  {@+x=z;
  if (starting_col > x) starting_col=x;
  @<Read and process \.{GF} commands until coming to the end of this row@>;
  } 

@ @d do_skip	z=0;paint_black=false
@d end_with(X)	{@+X;cur_gf=get_byte();goto done1;@+} 
@d five_cases(X)	case X: case X+1: case X+2: case X+3: case X+4
@d eight_cases(X)	case X: case X+1: case X+2: case X+3: case X+4: case X+5: case X+6: case X+7
@d thirty_two_cases(X)	eight_cases(X): eight_cases(X+8):
  eight_cases(X+16): eight_cases(X+24)
@d sixty_four_cases(X)	thirty_two_cases(X): thirty_two_cases(X+32)

@<Read and process...@>=
loop@+{@+resume: switch (cur_gf) {
  sixty_four_cases(0): k=cur_gf;@+break;
  case paint1: k=get_byte();@+break;
  case paint2: k=get_two_bytes();@+break;
  case paint3: k=get_three_bytes();@+break;
  case eoc: goto done1;
  case skip0: end_with(blank_rows=0;do_skip)@;
  case skip1: end_with(blank_rows=get_byte();do_skip)@;
  case skip2: end_with(blank_rows=get_two_bytes();do_skip)@;
  case skip3: end_with(blank_rows=get_three_bytes();do_skip)@;
  sixty_four_cases(new_row_0): sixty_four_cases(new_row_0+64):
   thirty_two_cases(new_row_0+128): five_cases(new_row_0+160):
    end_with(z=cur_gf-new_row_0;paint_black=true)@;
  case xxx1: case xxx2: case xxx3: case xxx4: case yyy: case no_op: {@+skip_nop();goto resume;
    } 
  default:bad_gf("Improper opcode")@;
  } @/
  @<Paint |k| bits and read another command@>;
  } 
done1: 

@ @<Paint |k| bits and read another command@>=
if (x+k > finishing_col) finishing_col=x+k;
if (paint_black) for (j=x; j<=x+k-1; j++) a[j]=a[j]+l;
paint_black=!paint_black;
x=x+k;
cur_gf=get_byte()

@ When the current row has been typeset, all entries of |a| will be even;
we want to divide them by~2 and incorporate a new row with $l=2^{11}$.
However, if they are all multiples of~4, we actually want to divide by~4
and incorporate two new rows, with $l=2^{10}$ and $l=2^{11}$. In general,
we want to divide by the maximum possible power of~2 and add the corresponding
number of new rows; that's where the |rho|~array comes in handy:

@<Advance to the next row that needs to be typeset; or |return|, if we're all done@>=
l=rho[a[starting_col]];
for (j=starting_col+1; j<=finishing_col; j++) if (l > rho[a[j]]) l=rho[a[j]];
if (l==4096) 
  if (cur_gf==eoc) return;
  else{@+y=y-blank_rows;blank_rows=0;l=1;
    starting_col=z;finishing_col=z;
    } 
else{@+while (a[starting_col]==0) incr(starting_col);
  while (a[finishing_col]==0) decr(finishing_col);
  for (j=starting_col; j<=finishing_col; j++) a[j]=a[j]/l;
  l=4096/l;
  } 

@ We now have constructed the major components of the necessary routine;
it simply remains to glue them all together in the proper framework.

@p void do_pixels(void)
{@+
bool @!paint_black; /*the paint switch*/ 
uint16_t @!starting_col, @!finishing_col; /*currently nonzero area*/ 
int @!j; /*for traversing that area*/ 
int @!l; /*power of two used to manipulate bit patterns*/ 
four_quarters @!i; /*character information word*/ 
eight_bits @!v; /*character corresponding to a pixel pattern*/ 
select_font(gray_font);
delta_x=delta_x+round(unsc_x_ratio*min_x);
for (j=0; j<=max_x-min_x; j++) a[j]=0;
l=1;z=0;starting_col=0;finishing_col=0;y=max_y+12;paint_black=false;
blank_rows=0;cur_gf=get_byte();
loop@+{@+@<Add more rows...@>;
  dvi_goto(0, delta_y-round(unsc_y_ratio*y));@<Typeset the pixels...@>;
  dvi_out(pop);@<Advance to the next...@>;
  } 
} 

@*The main program.
Now we are ready to put it all together. This is where \.{GFtoDVI} starts,
and where it ends.

@p int main(int argc, char **argv) { if (argc != 2) return 2;
if ((output=fopen(argv[1],"w"))==NULL) return 2;
initialize(); /*get all variables initialized*/
@<Initialize the strings@>;
start_gf(); /*open the input and output files*/ 
@<Process the preamble@>;
cur_gf=get_byte();init_str_ptr=str_ptr;
loop@+{@+@<Initialize variables for the next character@>;
  while ((cur_gf >= xxx1)&&(cur_gf <= no_op)) @<Process a no-op command@>;
  if (cur_gf==post) @<Finish the \.{DVI} file and |goto final_end|@>;
  if (cur_gf!=boc) if (cur_gf!=boc1) abort("Missing boc!");
@.Missing boc@>
  @<Process a character@>;
  cur_gf=get_byte();str_ptr=init_str_ptr;pool_ptr=str_start[str_ptr];
  } 
return 0; }

@ The main program needs a few global variables in order to do its work.

@<Glob...@>=
int @!k, @!m, @!p, @!q, @!r, @!s, @!t, @!dx, @!dy; /*general purpose registers*/ 
str_number @!time_stamp; /*the date and time when the input file was made*/ 
bool @!use_logo; /*should \MF's logo be put on the title line?*/ 

@ \MF\ sets the opening string to 32 bytes that give date and time as follows:
$$\hbox{|" METAFONT output yyyy.mm.dd:tttt"|}$$
We copy this to the \.{DVI} file, but remove the `\.{METAFONT}' part so that
it can be replaced by its proper logo.

@<Process the preamble@>=
if (get_byte()!=pre) bad_gf("No preamble");
@.No preamble@>
if (get_byte()!=gf_id_byte) bad_gf("Wrong ID");
@.Wrong ID@>
k=get_byte(); /*|k| is the length of the initial string to be copied*/ 
for (m=1; m<=k; m++) append_char(get_byte());
dvi_out(pre);dvi_out(dvi_id_byte); /*output the preamble*/ 
dvi_four(25400000);dvi_four(473628672); /*conversion ratio for sp*/ 
dvi_four(1000); /*magnification factor*/ 
dvi_out(k);use_logo=false;s=str_start[str_ptr];
for (m=1; m<=k; m++) dvi_out(str_pool[s+m-1]);
if (str_pool[s]==' ') 
 if (str_pool[s+1]=='M') 
  if (str_pool[s+2]=='E') 
   if (str_pool[s+3]=='T') 
    if (str_pool[s+4]=='A') 
     if (str_pool[s+5]=='F') 
      if (str_pool[s+6]=='O') 
       if (str_pool[s+7]=='N') 
        if (str_pool[s+8]=='T') 
    {@+incr(str_ptr);str_start[str_ptr]=s+9;use_logo=true;
    }  /*we will substitute `\MF' for \.{METAFONT}*/ 
time_stamp=make_string()

@*System-dependent changes.
This section should be replaced, if necessary, by changes to the program
that are necessary to make \.{GFtoDVI} work at a particular installation.
It is usually best to design your change file so that all changes to
previous sections preserve the section numbering; then everybody's version
will be consistent with the printed program. More extensive changes,
which introduce new sections, can be inserted here; then only the index
itself will get a new section number.
@^system dependencies@>

@*Index.
Here is a list of the section numbers where each identifier is used.
Cross references to error messages and a few other tidbits of information
also appear.

@ Appendix: Replacement of the string pool file.
@d str_0_255 	"^^@@^^A^^B^^C^^D^^E^^F^^G^^H^^I^^J^^K^^L^^M^^N^^O"@/
	"^^P^^Q^^R^^S^^T^^U^^V^^W^^X^^Y^^Z^^[^^\\^^]^^^^^_"@/
	" !\"#$%&'()*+,-./"@/
	"0123456789:;<=>?"@/
	"@@ABCDEFGHIJKLMNO"@/
	"PQRSTUVWXYZ[\\]^_"@/
	"`abcdefghijklmno"@/
	"pqrstuvwxyz{|}~^^?"@/
	"^^80^^81^^82^^83^^84^^85^^86^^87^^88^^89^^8a^^8b^^8c^^8d^^8e^^8f"@/
	"^^90^^91^^92^^93^^94^^95^^96^^97^^98^^99^^9a^^9b^^9c^^9d^^9e^^9f"@/
	"^^a0^^a1^^a2^^a3^^a4^^a5^^a6^^a7^^a8^^a9^^aa^^ab^^ac^^ad^^ae^^af"@/
	"^^b0^^b1^^b2^^b3^^b4^^b5^^b6^^b7^^b8^^b9^^ba^^bb^^bc^^bd^^be^^bf"@/
	"^^c0^^c1^^c2^^c3^^c4^^c5^^c6^^c7^^c8^^c9^^ca^^cb^^cc^^cd^^ce^^cf"@/
	"^^d0^^d1^^d2^^d3^^d4^^d5^^d6^^d7^^d8^^d9^^da^^db^^dc^^dd^^de^^df"@/
	"^^e0^^e1^^e2^^e3^^e4^^e5^^e6^^e7^^e8^^e9^^ea^^eb^^ec^^ed^^ee^^ef"@/
	"^^f0^^f1^^f2^^f3^^f4^^f5^^f6^^f7^^f8^^f9^^fa^^fb^^fc^^fd^^fe^^ff"@/
@d str_start_0_255	0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45,@/
	48, 51, 54, 57, 60, 63, 66, 69, 72, 75, 78, 81, 84, 87, 90, 93,@/
	96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111,@/
	112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,@/
	128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143,@/
	144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,@/
	160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175,@/
	176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191,@/
	194, 198, 202, 206, 210, 214, 218, 222, 226, 230, 234, 238, 242, 246, 250, 254,@/
	258, 262, 266, 270, 274, 278, 282, 286, 290, 294, 298, 302, 306, 310, 314, 318,@/
	322, 326, 330, 334, 338, 342, 346, 350, 354, 358, 362, 366, 370, 374, 378, 382,@/
	386, 390, 394, 398, 402, 406, 410, 414, 418, 422, 426, 430, 434, 438, 442, 446,@/
	450, 454, 458, 462, 466, 470, 474, 478, 482, 486, 490, 494, 498, 502, 506, 510,@/
	514, 518, 522, 526, 530, 534, 538, 542, 546, 550, 554, 558, 562, 566, 570, 574,@/
	578, 582, 586, 590, 594, 598, 602, 606, 610, 614, 618, 622, 626, 630, 634, 638,@/
	642, 646, 650, 654, 658, 662, 666, 670, 674, 678, 682, 686, 690, 694, 698, 702,@/
