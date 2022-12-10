@x
@h
@y
#include <string.h>
#define home_font_area_str "/home/user/tex/TeXfonts/"
@h
@z

@x
enum {@+@!file_name_size=50@+}; /*a file name shouldn't be longer than this*/
@y
enum {@+@!file_name_size=65@+}; /*a file name shouldn't be longer than this*/
@z

@x
l=9;init_str9('T')('e')('X')('f')('o')('n')('t')('s')(':')(home_font_area);@/
@y
strncpy(str_pool+pool_ptr, home_font_area_str, sizeof home_font_area_str - 1);
pool_ptr += sizeof home_font_area_str - 1;
str_start[++str_ptr] = pool_ptr;
@z

@x
else{@+if ((c=='>')||(c==':'))
@y
else{@+if (c=='/')
@z
