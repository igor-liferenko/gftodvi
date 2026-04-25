@x
@h
@y
@h
#define init_str(X) l = strlen(X); assert(l <= terminal_line_length); \
                    for (char *p = X; *p!='\0'; p++) buffer[l--] = *p; \
                    l = strlen(X); first_string
@z

@x
{ reset(gf_file, name_of_file);
@y
{ reset(gf_file, name_of_file); assert(gf_file.f!=NULL); assert(!ferror(gf_file.f));
@z

@x
{ reset(tfm_file, name_of_file);
@y
{ reset(tfm_file, name_of_file); assert(tfm_file.f!=NULL); assert(!ferror(tfm_file.f));
@z

@x
{ rewrite(dvi_file, name_of_file);
@y
{ rewrite(dvi_file, name_of_file); assert(dvi_file.f!=NULL);
@z

@x
l=9;init_str9('T')('e')('X')('f')('o')('n')('t')('s')(':')(home_font_area);
@y
l=9;init_str9('T')('e')('X')('f')('o')('n')('t')('s')('/')(home_font_area);
@z

@x
else{ if ((c=='>')||(c==':'))
@y
else{ if (c=='/')
@z

@x
uint8_t name_length; /*number of characters packed*/
@y
int name_length; /*number of characters packed*/
@z
