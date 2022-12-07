FEATURES := simd_backend serde rand_core

doc:
	cargo +nightly rustdoc --features "$(FEATURES)" -- --html-in-header docs/assets/rustdoc-include-katex-header.html --cfg docsrs

doc-internal:
	cargo +nightly rustdoc --features "$(FEATURES)" -- --html-in-header docs/assets/rustdoc-include-katex-header.html --document-private-items --cfg docsrs

