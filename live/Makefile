DIRS=stlc stlc-check stlc-lec9-start stlc-spine
HTMLS=html/bb2.html html/Gentzen.html html/euclidean.html html/exercises3.html \
      html/Id5.html html/deduction.html html/checksize.html \
      html/peirce.html html/typetype.html html/xirule.html \
      html/minimalrules.html html/selfcontained.html \
      html/arith1.html html/arithexp.html html/operational.html \
      html/compiler.html html/compiler2.html

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
