# all sources needed to build the paper
SOURCES = $(wildcard *.tex *.cls *.sty *.bib)
# sources for the arxiv version
ARXIV_SOURCES = $(filter-out $(wildcard *icfp*),$(wildcard *.tex *.cls *.sty *.bib *.bbl))
# sources for the camera-ready version
CPP_SOURCES = cpp25-sort-final.tex $(filter-out $(wildcard *arxiv*)$(wildcard *icfp*),$(wildcard *.tex *.cls *.sty *.bib *.bbl))
# targets to build: full paper, and the stripped submission
TARGETS = arxiv-sort.tex cpp25-sort-strip.tex cpp25-sort.pdf cpp25-sort-submission.pdf
# latexmk setup
DEPS_DIR = .deps
ENGINE = -pdf
LATEXMK = latexmk -recorder -use-make $(ENGINE)
# helper programs
PDFTK = pdftk

all: $(TARGETS)

cpp25-sort-strip.tex: cpp25-sort.tex
	cp -f $< $@

cpp25-sort.pdf: $(SOURCES)
	$(LATEXMK) cpp25-sort.tex

arxiv-sort.tex: cpp25-sort.tex
	cp -f $< $@

arxiv-sort.pdf: ENGINE = -pdf
arxiv-sort.pdf: $(SOURCES)
	$(LATEXMK) arxiv-sort.tex

cpp25-sort-strip.pdf: $(SOURCES)
	$(LATEXMK) cpp25-sort-strip.tex

# Builds both full and stripped versions, counts the pages in the
# stripped version, then cuts that many pages from the full version
cpp25-sort-submission.pdf: cpp25-sort-strip.pdf cpp25-sort.pdf
	$(eval NUMPAGES=$(shell $(PDFTK) cpp25-sort-strip.pdf dump_data | grep NumberOfPages | grep -o -E '[[:digit:]]+'))
	@echo Number of pages in submission is: $(NUMPAGES)
	$(PDFTK) cpp25-sort.pdf cat 1-$(NUMPAGES) output cpp25-sort-submission.pdf

cont: continuous
continuous: LATEXMK += -f -interaction=nonstopmode -pvc
continuous: $(SOURCES)
	$(LATEXMK) cpp25-sort.tex

fast-continuous: LATEXMK += -f -interaction=nonstopmode -pvc
fast-continuous: $(SOURCES)
	$(LATEXMK) cpp25-sort-strip.tex

arxiv.tar.gz:
	tar achvf arxiv.tar.gz $(ARXIV_SOURCES)

cpp25-sort-final.pdf: $(SOURCES)
	$(LATEXMK) cpp25-sort-final.tex
	mv cpp25-sort-final.pdf cpp25-sort-final-full.pdf
	$(PDFTK) cpp25-sort-final-full.pdf cat 1-28 output cpp25-sort-final.pdf
	rm cpp25-sort-final-full.pdf

cpp25-sort-final.zip: $(SOURCES)
	zip cpp25-sort-final.zip $(CPP_SOURCES)

deploy: all
	rsync -avchzP cpp25-sort.pdf vikraman@internal.vikraman.org:_site/files/

fast-deploy: LATEXMK += -f -interaction=nonstopmode
fast-deploy: deploy

cont-deploy: continuous-deploy
continuous-deploy: $(SOURCES)
	watchman-make -p '**/*.tex' '**/*.bib' '**/*.cls' '**/*.sty' -t fast-deploy

clean:
	latexmk -c

distclean: clean
	latexmk -C
	rm -rf *.axp *.xcp *.bbl *.blg *.aux *.xml *.cut *.pdf

cache-clean:
	rm -rf `biber --cache`

.PHONY: clean distclean cache-clean cont continuous fast-continuous deploy fast-deploy cont-deploy continuous-deploy
