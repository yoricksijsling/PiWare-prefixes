SRC=src
INCLUDES=${AGDA_INCLUDES} \
         ${SRC} \
         ../piware-agda/src \
         ../agda-stdlib/src

AGDA_MODULES=PiWarePrefixes/Atom/Int8 \
             PiWarePrefixes/Circuit/Context/Core \
             PiWarePrefixes/Gates/Plus \
             PiWarePrefixes/MinGroups \
             PiWarePrefixes/Patterns/Core \
             PiWarePrefixes/Patterns/Fan \
             PiWarePrefixes/Patterns/HetSeq \
             PiWarePrefixes/Patterns/Stretch \
             PiWarePrefixes/Permutation \
             PiWarePrefixes/Plugs/Core \
             PiWarePrefixes/Simulation/Equality/Core \
             PiWarePrefixes/Simulation/Properties/Fans \
             PiWarePrefixes/Simulation/Properties/HetSeq \
             PiWarePrefixes/Simulation/Properties/Stretching/Derived \
             PiWarePrefixes/Simulation/Properties/Stretching \
             PiWarePrefixes/Simulation/Properties \
             PiWarePrefixes/Utils \

INCLUDE_PARAMS=$(INCLUDES:%=-i%$)

all: $(AGDA_MODULES:%=$(SRC)/%.agdai)


$(SRC)/%.agdai: $(SRC)/%.lagda
	agda $(INCLUDE_PARAMS) $<

$(SRC)/%.agdai: $(SRC)/%.agda
	agda $(INCLUDE_PARAMS) $<

clean:
	find . -name '*.agdai' -delete

.PHONY: clean
