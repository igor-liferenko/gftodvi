all:
	make -C web2w
	cp web2w/cgftodvi.w gftodvi.w
	tie -c gftodvi.ch gftodvi.w path.ch arg.ch comment.ch >/dev/null
	ctangle gftodvi gftodvi
	gcc gftodvi.c -o gftodvi -lm
