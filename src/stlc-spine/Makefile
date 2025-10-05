.PHONY: all
all: index.html html

.PHONY: html
html :
	agda --html Lecture8.agda

.PHONY: index.html
index.html :
	tree -H '.' -L 2 --noreport --charset utf-8 > $@

# EOF
