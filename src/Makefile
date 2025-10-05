.PHONY: all
all: html stlc index.html

.PHONY: html
html:
	agda --html Everything.agda

.PHONY: stlc
stlc:
	make -C stlc

.PHONY: index.html
index.html :
	tree -H '.' -L 2 --noreport --charset utf-8 > $@

# EOF
