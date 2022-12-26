@x
enum {@+@!file_name_size=50@+}; /*a file name shouldn't be longer than this*/
@y
enum {@+@!file_name_size=256@+}; /*a file name shouldn't be longer than this*/
@z

@x
l=9;init_str9('T')('e')('X')('f')('o')('n')('t')('s')(':')(home_font_area);@/
@y
for (char *p = "/home/user/tex/TeXfonts/"; *p; p++) append_char(*p);
l=0;init_str0(home_font_area);
@z

@x
else{@+if ((c=='>')||(c==':'))
@y
else{@+if (c=='/')
@z

@x
uint8_t @!name_length; /*number of characters packed*/ 
@y
uint16_t @!name_length; /*number of characters packed*/ 
@z
