FEATURES := serde rand_core digest

FLAGS := --cfg docsrs --cfg=curve25519_dalek_backend="simd"
export RUSTFLAGS := $(FLAGS)
export RUSTDOCFLAGS := $(FLAGS)

doc:
	cargo +nightly rustdoc --features "$(FEATURES)" --open -- --html-in-header docs/assets/rustdoc-include-katex-header.html

doc-internal:
	cargo +nightly rustdoc --features "$(FEATURES)" -- --html-in-header docs/assets/rustdoc-include-katex-header.html --document-private-items
