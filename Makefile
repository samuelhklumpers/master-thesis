AGDA=agda-2.6.2
AFLAGS=-i. --latex
SOURCE=Main.tex
# POSTPROCESS=postprocess-latex.pl
LATEX=latexmk -pdf -use-make -lualatex -synctex=1


.PHONY: all


targets := $(wildcard src/**/*.lagda)

lagda = $(AGDA) $(AFLAGS) $(target)


all:
	$(foreach target, $(targets), $(lagda) ; )
	cd latex/ && \
	$(LATEX) $(SOURCE)

# perl ../$(POSTPROCESS) $(SOURCE).tex > $(SOURCE).processed && \
# mv $(SOURCE).processed $(SOURCE).tex && \
