FEATURES := serde rand_core digest

export RUSTFLAGS := --cfg=curve25519_dalek_backend="simd"
export RUSTDOCFLAGS := --cfg docsrs

doc:
	cargo +nightly rustdoc --features "$(FEATURES)" -- --html-in-header docs/assets/rustdoc-include-katex-header.html

doc-internal:
	cargo +nightly rustdoc --features "$(FEATURES)" -- --html-in-header docs/assets/rustdoc-include-katex-header.html --document-private-items
