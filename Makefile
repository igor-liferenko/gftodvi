all:
	make -C web2w
	cp web2w/cgftodvi.w gftodvi.w
	tie -c gftodvi.ch gftodvi.w filename.ch path.ch paper+origin.ch >/dev/null
	ctangle gftodvi gftodvi
	gcc gftodvi.c -o gftodvi -lm
	cweave -f gftodvi && pdftex gftodvi >/dev/null
