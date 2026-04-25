@x
#include "pascal.tab.h"
@y
#include "pascal-gftodvi.tab.h"
@z

@x
wputs("\n@@ Appendix: Replacement of the string pool file.\n");
{ token *str_k;
  int i, k;
  @<generate definitions for the first 256 strings@>@;
  for (str_k=first_string;str_k != NULL;str_k=str_k->link)
    @<generate definition for string |k|@>@;
  @<generate string pool initializations@>@;
}
@y
@z
