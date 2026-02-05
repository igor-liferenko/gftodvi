all:
	ctangle web2w web2w-gftodvi
	patch -so web-gftodvi.l web.l web-gftodvi.patch
	flex -o web.lex.c web-gftodvi.l
	patch -so pascal-gftodvi.y pascal.y pascal-gftodvi.patch
	bison --warnings=none -d -v pascal-gftodvi.y
	gcc -o web2w web2w.c web.lex.c pascal-gftodvi.tab.c
	cp gftodvi.web gftodvi-web2w.web
	@sed -i '/@d five_cases/,+4s/+/,/g' gftodvi-web2w.web
	@sed -i 's/case boolean of/case two_choices of/;s/true:/1:/;s/false:/2:/' gftodvi-web2w.web
	@sed -i '/|packed$$/{N;s/|packed\nfile of 0..255|/\n/}' gftodvi-web2w.web
	./web2w -o cgftodvi.w gftodvi-web2w.web
	@sed -i '/@d five_cases/,+4s/: case/+/g' cgftodvi.w
	patch -s cgftodvi.w cgftodvi.patch
	@sed -i 's/@<Types\.\.\.@>=/@<Types ...@>=/' cgftodvi.w
