FEATURES := serde rand_core digest

export RUSTFLAGS := --cfg docsrs
export RUSTDOCFLAGS := --cfg=curve25519_dalek_backend="simd"

doc:
	cargo +nightly rustdoc --features "$(FEATURES)" --open -- --html-in-header docs/assets/rustdoc-include-katex-header.html

doc-internal:
	cargo +nightly rustdoc --features "$(FEATURES)" -- --html-in-header docs/assets/rustdoc-include-katex-header.html --document-private-items
