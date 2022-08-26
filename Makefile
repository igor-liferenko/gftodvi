all:
	make -C web2w
	cp web2w/cgftodvi.w gftodvi.w
	tie -c gftodvi.ch gftodvi.w filename.ch path.ch >/dev/null
	ctangle gftodvi gftodvi
	gcc gftodvi.c -o gftodvi -lm
	cweave -f -e gftodvi
	sed -i '/^char\\_info&/{s//&$$/;s/\\cr/$$&/}' gftodvi.tex
	sed -i '/^param&/{s//&$$/;s/\\cr/$$&/}' gftodvi.tex
	sed -i 's/{buffer}\[\(.*\)\]/{buffer}\\char`\\[\1\\char`\\]\\/' gftodvi.scn
	pdftex gftodvi >/dev/null
