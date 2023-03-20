SHELL:=/bin/bash -O globstar

AGDA=agda-2.6.2
# make sure we stop early if an unsolved meta is going to stop us later anyway
AFLAGS=-i. --latex

# make sure latex doesn't ask us for input if we hit an error
LATEX=latexmk -pdf -use-make -lualatex -halt-on-error -synctex=1
SOURCE=Main.tex



.PHONY: all bel
targets := $(shell ls src/**/*.lagda)


lagda = $(AGDA) $(AFLAGS) $(target)

all:
	$(MAKE) try ; tput bel

try:
	$(foreach target, $(targets), $(lagda) ; )
	cd latex/ && \
	$(LATEX) $(SOURCE)
