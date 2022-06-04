@x
@p void start_gf(void)
{@+
loop@+{@+print_nl("GF file name: ");input_ln();
@y
@p char **av; void start_gf(void)
{@+
  line_length=0;
  while (line_length < terminal_line_length && (*av)[line_length] != 0) {
    buffer[line_length] = (*av)[line_length]; incr(line_length);
  }
@z

@x
  }
@y
  exit(2);
@z

@x
@p int main(int argc, char **argv) { if (argc != 2) return 2;
@y
@p int main(int argc, char **argv) { if (argc != 3) return 2; av = argv + 2;
@z
