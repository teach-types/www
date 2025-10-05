DIRS=stlc stlc-lec9-start stlc-spine

.PHONY: all
all: index.html $(DIRS)

.PHONY: $(DIRS)
$(DIRS) : % :
	make -C $*

.PHONY: index.html
index.html :
	tree -H '.' -L 2 --noreport --charset utf-8 > $@

# EOF
