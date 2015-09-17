SRC := $(shell ls *.scala)
LEON := leon
FUNS ?=
TIMEOUT ?= 10
LEON_FLAGS = --timeout=$(TIMEOUT)

ifneq ($(FUNS),)
all: LEON_FLAGS += --functions=$(FUNS)
endif

all:
	$(LEON) $(LEON_FLAGS) $(SRC)

%:
	$(LEON) $(LEON_FLAGS) --functions=$@ $(SRC)

.PHONY: all
