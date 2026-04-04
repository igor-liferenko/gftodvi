@x
@h
@y
@h
#define init_str(X) l = strlen(X); assert(l <= terminal_line_length); \
                    for (char *p = X; *p; p++) buffer[l--] = *p; \
                    l = strlen(X); first_string
@z

@x
l=9;init_str9('T')('e')('X')('f')('o')('n')('t')('s')('/')(home_font_area);
@y
init_str("TeXfonts/")(home_font_area);
@z
