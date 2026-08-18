DIRS=stlc stlc-check stlc-spine

.PHONY: all
all: html index.html $(DIRS)

.PHONY: html
html:
	agda --html Everything.agda

.PHONY: $(DIRS)
$(DIRS) : % :
	make -C $*

.PHONY: index.html
index.html :
	tree -H '.' -L 2 --noreport --charset utf-8 > $@

# EOF
