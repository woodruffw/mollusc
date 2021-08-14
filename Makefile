.PHONY: all
all:
	@echo "This is not a real build system."

.PHONY: fmt
fmt:
	@# TODO(ww): Add +nightly here if available by checking `rustup toolchain list`
	cargo fmt

.PHONY: lint
lint:
	cargo clippy -- \
		-D warnings \
		-D clippy::expect_used \
		-D clippy::unwrap_used \
		-D clippy::panic
	@# NOTE(ww): run docs here too, since they can fail the CI when links are broken
	cargo doc
