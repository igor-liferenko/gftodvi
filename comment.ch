If comment was added by comment.ch from mf repo, do not use it in hardcopy proofs.

@x
for (m=1; m<=k; m++) dvi_out(str_pool[s+m-1]);
@y
for (m=1; m<=k; m++) dvi_out(str_pool[s+m-1]);
int $ = 0;
for (m=1; m<=k; m++) {
  if (str_pool[s+m-1] == ' ') $++;
  if ($ == 4) $++, pool_ptr = s+m-1;
}
@z
