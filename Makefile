ROCQMAKEFILE ?= rocq makefile --no-rocq-package-warning
PROJECT    := _RocqProject
GENERATED  := Makefile.rocq

.PHONY: all clean html validate

all: $(GENERATED)
	$(MAKE) -f $(GENERATED)

html: $(GENERATED)
	$(MAKE) -f $(GENERATED) html

validate: $(GENERATED)
	$(MAKE) -f $(GENERATED) validate

$(GENERATED): $(PROJECT)
	$(ROCQMAKEFILE) -f $(PROJECT) -o $(GENERATED)

clean:
	@if [ -f $(GENERATED) ]; then $(MAKE) -f $(GENERATED) cleanall; fi
	rm -f $(GENERATED) $(GENERATED).conf
