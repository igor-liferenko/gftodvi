@x
@p void input_ln(void) /*inputs a line from the terminal*/ 
{@+update_terminal;if(!term_in.f)term_in.f=stdin,get(term_in);
if (eoln(term_in)) read_ln(term_in);
line_length=0;
while ((line_length < terminal_line_length)&&!eoln(term_in)) 
  {@+buffer[line_length]=xord[term_in.d];incr(line_length);get(term_in);
  } 
} 
@y
@p
char **av;
int ac;
void input_ln(void)
{
  strcpy(buffer, *av);
  line_length = strlen(*av);
  av++, ac--;
} 
@z

@x
loop@+{@+print_nl("GF file name: ");input_ln();
@y
loop@+{@+input_ln(); if (ac) interaction = true;
@z

@x
loop@+{@+not_found: print_nl("Special font substitution: ");
@y
loop@+{@+not_found:
@z

@x
  print("OK; any more? ");goto resume;
@y
  if (!ac) goto done;
@z
  
@x
@p int main(int argc, char **argv) { if (argc != 2) return 2;
@y
@p int main(int argc, char **argv) { if (argc < 3) return 2; av = argv + 2; ac = argc - 2;
@z
