@x
dvi_out(k);use_logo=false;s=str_start[str_ptr];
for (m=1; m<=k; m++) dvi_out(str_pool[s+m-1]);
@y
char *geometry = "55380990x39158276+3729359+3729359";
//                 297mm    210mm    20mm    20mm
dvi_out(k+1+strlen(geometry));use_logo=false;s=str_start[str_ptr];
for (m=1; m<=k; m++) dvi_out(str_pool[s+m-1]);
dvi_out(' ');
while (*geometry) dvi_out(*geometry++);
@z
