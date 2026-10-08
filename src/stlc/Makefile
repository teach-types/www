.PHONY: default
default: index.html html

.PHONY: all
all: index.html html test

.PHONY: html
html :
	agda --html Lecture8.agda
	agda --html Lecture8NoPeirce.agda
	agda --html Lecture9.agda
	agda --html Lecture10.agda
	agda --html Everything.agda

.PHONY: index.html
index.html :
	tree -H '.' -L 2 --noreport --charset utf-8 > $@

.PHONY: test
test: stlc
	./stlc examples/add.hs

.PHONY: stlc
stlc:
	agda --compile stlc.agda

# EOF
