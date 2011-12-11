LHS_FILE=$(wildcard *.lhs)
TEX_FILE=$(LHS_FILE:.lhs=.tex)
NOTES_FILE=notes.$(TEX_FILE)
SLIDE_FILE=slide.$(TEX_FILE)
GENERATED=$(TEX_FILE) $(NOTES_FILE:.tex=.pdf) $(SLIDE_FILE:.tex=.pdf) $(NOTES_FILE) $(SLIDE_FILE)

all: slides notes

slides: $(TEX_FILE)
	cat slides.header $(TEX_FILE) > $(SLIDE_FILE)
	rubber --pdf $(SLIDE_FILE)

notes: $(TEX_FILE)
	cat notes.header $(TEX_FILE) > $(NOTES_FILE)
	rubber --pdf $(NOTES_FILE)

$(TEX_FILE): $(LHS_FILE)
	@echo $(LHS_FILE)
	lhs2TeX $(LHS_FILE) > $(TEX_FILE)

# ways for showing on OSX/Linux
pdfshow: notes
	if [ -x `which xpdf` ]  ; then xpdf $(NOTES_FILE:.tex=.pdf); fi &
	if [ -x /usr/bin/open ] ; then open $(NOTES_FILE:.tex=.pdf); fi

clean:
	# never randomly delete .tex or .pdf files, specify them separately.
	-rm -f *.toc *.aux *.snm *.blg *.bbl *.nav *.out *.ptb *.log
	-rm -f $(GENERATED)

.PHONY: pdfshow $(TEX_FILE) clean
