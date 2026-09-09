DIRS=stlc stlc-check stlc-lec9-start stlc-spine
HTMLS=html/bb2.html html/Gentzen.html html/euclidean.html html/exercises3.html

.PHONY: all
all: index.html $(DIRS) $(HTMLS)

.PHONY: $(DIRS)
$(DIRS) : % :
	make -C $*

.PHONY: index.html
index.html :
	tree -H '.' -L 2 --noreport --charset utf-8 > $@

html/%.html : %.agda
	agda --html $<

# EOF
