# Makefile for www structure of the Types course

# sed: Insert <br/> tags if line ends with punctuation.
# Do this via trailing spaces (markdown syntax for line break).
# (This then does no harm if inside code block.)
# Inside Makefile, need to use $$ for eol ($).
index.html : README.md Makefile pandoc.css
	sed -e 's#\([.,;:!?]\)$$#\1  #' $< | pandoc --toc --toc-depth 1 --css pandoc.css -f markdown -t html -o $@ --standalone
# --metadata title="Types for Programs and Proofs"  ## This also adds a title to the rendering

## Cleaning

clean : clean_index

clean_index :
	rm -f index.html

# EOF
