SRC=src
INCLUDES=${AGDA_INCLUDES} \
         ${SRC} \
         ../piware-agda/src \
         ../agda-stdlib/src

AGDA_MODULES=PiWarePrefixes/Gates/Plus \
             PiWarePrefixes/Patterns/Core \
             PiWarePrefixes/Plugs/Core \
             PiWarePrefixes/Samples/Fan


INCLUDE_PARAMS=$(INCLUDES:%=-i%$)

all: $(AGDA_MODULES:%=$(SRC)/%.agdai)


$(SRC)/%.agdai: $(SRC)/%.lagda
	agda $(INCLUDE_PARAMS) $<

$(SRC)/%.agdai: $(SRC)/%.agda
	agda $(INCLUDE_PARAMS) $<

clean:
	find . -name '*.agdai' -delete

.PHONY: clean
