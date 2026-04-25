all:
	tie -c web2w.ch web2w.w tab.ch web2w-gftodvi.ch at-gftodvi.ch >/dev/null
	ctangle web2w web2w
	patch -so web-gftodvi.l web.l web-gftodvi.patch
	flex -o web.lex.c web-gftodvi.l
	patch -so pascal-gftodvi.y pascal.y pascal-gftodvi.patch
	bison --warnings=none -d -v pascal-gftodvi.y
	gcc -o web2w web2w.c web.lex.c pascal-gftodvi.tab.c
	cp gftodvi.web gftodvi-web2w.web
	@sed -i "s/\([(,]\)'\(.\)'/\1'\2_'/g" gftodvi-web2w.web
	@sed -i '/@d five_cases/,+4s/+/,/g' gftodvi-web2w.web
	@sed -i 's/@<Types /@<Types_/' gftodvi-web2w.web
	@sed -i 's/case boolean of/case two_choices of/;s/true:/1:/;s/false:/2:/' gftodvi-web2w.web
	@sed -i 's/|packed file of 0..255|//' gftodvi-web2w.web
	./web2w -o cgftodvi.w gftodvi-web2w.web
	@sed -i 's/"\(.\)_"/"\1"/g' cgftodvi.w
	@sed -i '/@d five_cases/,+4s/: case/+/g' cgftodvi.w
	@sed -i 's/@<Types_/@<Types /' cgftodvi.w
	patch -s cgftodvi.w cgftodvi.patch
