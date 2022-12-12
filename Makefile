FEATURES := serde rand_core digest

doc:
	cargo +nightly rustdoc --features "$(FEATURES)" -- --html-in-header docs/assets/rustdoc-include-katex-header.html --cfg docsrs --cfg=curve25519_dalek_backend=\"simd\"

doc-internal:
	cargo +nightly rustdoc --features "$(FEATURES)" -- --html-in-header docs/assets/rustdoc-include-katex-header.html --document-private-items --cfg docsrs --cfg=curve25519_dalek_backend=\"simd\"
