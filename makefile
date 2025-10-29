DUNE ?= dune
PROFILE ?= dev
COV_DIR ?= _coverage

.PHONY: all build test coverage clean help

all: build

build:
	$(DUNE) build --profile $(PROFILE)

test:
	$(DUNE) runtest --profile $(PROFILE)

coverage:
	$(DUNE) clean
	$(DUNE) runtest --force --instrument-with bisect_ppx --profile $(PROFILE)
	bisect-ppx-report html -o $(COV_DIR)
	@echo ""
	@echo "Coverage report : $(COV_DIR)/index.html"

clean:
	$(DUNE) clean
	rm -rf $(COV_DIR)