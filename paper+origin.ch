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
char *geometry = getenv("geometry");
if (geometry) dvi_out(k+1+strlen(geometry)) else
dvi_out(k);use_logo=false;s=str_start[str_ptr];
for (m=1; m<=k; m++) dvi_out(str_pool[s+m-1]);
if (geometry) {
  dvi_out(' ');
  while (*geometry) dvi_out(*geometry++);
}
@z
