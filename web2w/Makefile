all:
	ctangle web2w web2w-gftodvi
	patch -so web-gftodvi.l web.l web-gftodvi.patch
	flex -o web.lex.c web-gftodvi.l
	patch -so pascal-gftodvi.y pascal.y pascal-gftodvi.patch
	bison --warnings=none -d -v pascal-gftodvi.y
	gcc -o web2w web2w.c web.lex.c pascal-gftodvi.tab.c
	@sed '1593s/file/File/;4245,4249s/+/,/g;1763,1766{s/^@!/two_choices = 1..2;\n&/;s/boolean/two_choices/;s/true/1/;s/false/2/}' gftodvi.web >gftodvi-web2w.web
	./web2w -o cgftodvi.w gftodvi-web2w.web
	patch -s cgftodvi.w cgftodvi.patch
	@sed -i 's/@<Types\.\.\.@>=/@<Types ...@>=/' cgftodvi.w
	@weave gftodvi >/dev/null && sed -i 1s/webmac/pwebmac/ gftodvi.tex
