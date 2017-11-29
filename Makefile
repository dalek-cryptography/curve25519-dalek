
doc:
	cargo rustdoc --features "nightly yolocrypto" -- --html-in-header rustdoc-include-katex-header.html

doc-internal:
	cargo rustdoc --features "nightly yolocrypto" -- --html-in-header rustdoc-include-katex-header.html --document-private-items

