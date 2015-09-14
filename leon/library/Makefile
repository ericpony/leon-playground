SRC := delete.scala distinct.scala min.scala permutation.scala \
	sorted-list.scala
LEON := leon
FUNS ?=
TIMEOUT ?= 5
LEON_FLAGS = --timeout=$(TIMEOUT)

ifneq ($(FUNS),)
all: LEON_FLAGS += --functions=$(FUNS)
endif

all:
	$(LEON) $(LEON_FLAGS) $(SRC)

%:
	$(LEON) $(LEON_FLAGS) --functions=$@ $(SRC)

.PHONY: all
