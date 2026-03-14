all:
	make -C web2w
	tie -m gftodvi.w web2w/cgftodvi.w web2w/cgftodvi.ch >/dev/null
	tie -c gftodvi.ch gftodvi.w path.ch arg.ch comment.ch >/dev/null
	ctangle gftodvi gftodvi
	gcc gftodvi.c -o gftodvi -lm
