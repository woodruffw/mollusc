HAS_NIGHTLY := $(shell rustup toolchain list | grep nightly)
ifeq ($(HAS_NIGHTLY),)
	FMT_FLAG :=
else
	FMT_FLAG := +nightly
endif

.PHONY: all
all:
	@echo "This is not a real build system."

.PHONY: fmt
fmt:
	cargo $(FMT_FLAG) fmt

.PHONY: lint
lint:
	cargo clippy -- \
		-D warnings \
		-D clippy::expect_used \
		-D clippy::unwrap_used \
		-D clippy::panic
	@# NOTE(ww): run docs here too, since they can fail the CI when links are broken
	cargo doc
