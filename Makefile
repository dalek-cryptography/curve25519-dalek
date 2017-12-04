FEATURES := nightly yolocrypto

doc:
	cargo rustdoc --features "$(FEATURES)" -- --html-in-header rustdoc-include-katex-header.html

doc-internal:
	cargo rustdoc --features "$(FEATURES)" -- --html-in-header rustdoc-include-katex-header.html --document-private-items

