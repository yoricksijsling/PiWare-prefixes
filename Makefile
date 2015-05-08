SRC=src
SRC_PIWARE=../piware-agda/src

INCLUDES=${AGDA_INCLUDES} \
         ${SRC} \
         ${SRC_PIWARE} \
         ../agda-stdlib/src

MODULES_PIWARE=PiWare/Circuit

MODULES=Report \
        Data/Vec/Equality/Indexed \
        PiWarePrefixes/Atom/Int8 \
        PiWarePrefixes/Circuit/Context/Core \
        PiWarePrefixes/Circuit/Monoid \
        PiWarePrefixes/Gates/Plus \
        PiWarePrefixes/MinGroups \
        PiWarePrefixes/Patterns/Core \
        PiWarePrefixes/Patterns/Fan \
        PiWarePrefixes/Patterns/HetSeq \
        PiWarePrefixes/Patterns/Scan \
        PiWarePrefixes/Patterns/Stretch \
        PiWarePrefixes/Permutation \
        PiWarePrefixes/Plugs/Core \
        PiWarePrefixes/Simulation/Equality/Core \
        PiWarePrefixes/Simulation/Properties/Fans \
        PiWarePrefixes/Simulation/Properties/HetSeq \
        PiWarePrefixes/Simulation/Properties/Scans/Derived \
        PiWarePrefixes/Simulation/Properties/Scans/SuccProp \
        PiWarePrefixes/Simulation/Properties/Scans \
        PiWarePrefixes/Simulation/Properties/Stretching/Derived \
        PiWarePrefixes/Simulation/Properties/Stretching \
        PiWarePrefixes/Simulation/Properties \
        PiWarePrefixes/Utils

SOURCEFILES=$(MODULES_PIWARE:%=$(SRC_PIWARE)/%) $(MODULES:%=$(SRC/%))
MODULES_ALL=$(MODULES_PIWARE) $(MODULES)

INCLUDE_PARAMS=$(INCLUDES:%=-i%$)

default: code
all: code report
clean: cleancode cleanreport

# Code --------------------

code: $(SOURCEFILES:%=%.agdai)

$(SRC_PIWARE)/%.agdai: $(SRC_PIWARE)/%.lagda
	agda $(INCLUDE_PARAMS) $<

$(SRC)/%.agdai: $(SRC)/%.lagda
	agda $(INCLUDE_PARAMS) $<
$(SRC)/%.agdai: $(SRC)/%.agda
	agda $(INCLUDE_PARAMS) $<

cleancode:
	find $(SRC_PIWARE) -name '*.agdai' -delete
	find $(SRC) -name '*.agdai' -delete

# Report --------------------

report: AGDA_PARAMS = $(INCLUDE_PARAMS) --latex-dir=latex --latex --allow-unsolved-metas
report: report/main.pdf

latex/%.tex: $(SRC_PIWARE)/%.lagda
	agda $(AGDA_PARAMS) $<
latex/%.tex: $(SRC)/%.lagda
	agda $(AGDA_PARAMS) $<

report/main.pdf: $(MODULES_ALL:%=latex/%.tex) latex/agda.sty report/main.tex report/body.tex
	latexmk -xelatex -cd report/main.tex

cleanreport:
	rm -rf latex/**/*.tex
	latexmk -c report/main.tex


.PHONY: default all clean code cleancode report cleanreport
