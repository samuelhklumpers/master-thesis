SHELL:=/bin/bash -O globstar

AGDA=agda-2.6.2
# make sure we stop early if an unsolved meta is going to stop us later anyway
AFLAGS=-i. --latex

# make sure latex doesn't ask us for input if we hit an error
LATEX=latexmk -pdf -use-make -lualatex -halt-on-error -synctex=1
SOURCE=Main.tex
FAST=false

.PHONY: all bel fast

# naive fix 
targets := $(shell git status | grep .lagda$$ | grep -v deleted | grep -v Notes | awk -F 'src/' '{print "src/"$$2}')

lagda=$(AGDA) $(AFLAGS)

all:
	$(MAKE) try ; tput bel

fast:
	$(eval FAST=true)
	$(MAKE) all -e FAST=$(FAST)

try:
ifeq ($(FAST), true)
	$(eval lagda=$(lagda) --only-scope-checking)
endif
	echo $(targets)
	$(foreach target, $(targets), $(lagda) $(target) && ) :
	cd latex/ && \
	$(LATEX) $(SOURCE)