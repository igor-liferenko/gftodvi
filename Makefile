all:
	make -C web2w
	cp web2w/cgftodvi.w gftodvi.w
	tie -c gftodvi.ch gftodvi.w paper+origin.ch path.ch arg.ch >/dev/null
	ctangle gftodvi gftodvi
	gcc gftodvi.c -o gftodvi -lm
