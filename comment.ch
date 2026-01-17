If environment variable 'gftodvi_comment' is set, append its value to comment of
output DVI file (separated by space).

@x
@h
@y
#include <string.h>
@h
@z

@x
dvi_out(k);use_logo=false;s=str_start[str_ptr];
for (m=1; m<=k; m++) dvi_out(str_pool[s+m-1]);
@y
char *dvi_comment = getenv("gftodvi_comment");
if (dvi_comment) dvi_out(k+1+strlen(dvi_comment)) else
dvi_out(k);use_logo=false;s=str_start[str_ptr];
for (m=1; m<=k; m++) dvi_out(str_pool[s+m-1]);
if (dvi_comment) {
  dvi_out(' ');
  while (*dvi_comment) dvi_out(*dvi_comment++);
}
@z
