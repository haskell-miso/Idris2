# The bootstrap compiler doesn't know two-level type theory, so the bootstrap
# build of base (see bootstrap-stage2.sh) leaves out Language.Staged. The full
# base is rebuilt with the new compiler afterwards.
BASE_IPKG ?= base.ipkg

all: build
.PHONY: all

bootstrap-base.ipkg: base.ipkg
	grep -v 'Language\.Staged' base.ipkg > $@

build: ${BASE_IPKG}
	${IDRIS2} --build ${BASE_IPKG}
.PHONY: build

install: ${BASE_IPKG}
	${IDRIS2} --install ${BASE_IPKG}
.PHONY: install

install-with-src:
	${IDRIS2} --install-with-src ${BASE_IPKG}
.PHONY: install-with-src

docs:
	${IDRIS2} --mkdoc ${BASE_IPKG}
.PHONY: docs

clean:
	$(RM) -r build bootstrap-base.ipkg
.PHONY: clean
