include GNUmakefile.conf

#################
#   General     #
#################

.PHONY: default
default: build

.PHONY: all
all: build

.PHONY: build
build:
	dune build --profile release

dpll: build
	ln -s _build/install/default/bin/dpll dpll || true

.PHONY: doc
doc:
	dune build @doc

.PHONY: clean
clean:
	dune clean
	@rm -rf $(FIRSTNAME)_$(LASTNAME).tar.gz

TIMEOUT=30
SUDOKUSTART=0
NSUDOKU=10

#################
#      DPLL     #
#################


.PHONY: tests
tests: build dpll
	./tests/run.sh $(TIMEOUT)

.PHONY: tests_new
tests_new: build dpll
	./tests/run_new.sh $(TIMEOUT)

#################
#     Sudoku    #
#################

.PHONY: sudoku
sudoku: build dpll
	./sudoku/run.sh $(TIMEOUT) $(SUDOKUSTART) $(NSUDOKU)
