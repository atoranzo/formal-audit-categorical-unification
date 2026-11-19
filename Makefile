# Verification of the archive; see README.md. Run from the root of the archive.
#   make verify                  every check: checksums, Lean, Python, Lean with Mathlib
#   make verify SKIP_MATHLIB=1   the same, without the Lean project with Mathlib
#   make checksums               only the SHA-256 sums of the files (SHA256SUMS)
#   make verify-lean             only the seven Lean files without Mathlib
#   make verify-python           only the fifteen Python scripts
#   make verify-mathlib          only the Lean project with Mathlib (eight modules)
#   make pdf                     rebuild the paper as build/paper/main.pdf
#   make clean                   remove build/
.PHONY: help verify checksums verify-lean verify-python verify-mathlib pdf clean

help:
	@sed -n 's/^#   //p' Makefile

verify:
	bash verify_all.sh

checksums:
	@if command -v sha256sum > /dev/null 2>&1; then sha256sum -c --quiet SHA256SUMS; \
	 else shasum -a 256 -c --quiet SHA256SUMS; fi && echo "OK    all files match SHA256SUMS"

verify-lean:
	bash lean/verify_lean.sh

verify-python:
	bash python/verify_python.sh

verify-mathlib:
	bash lean-mathlib/verify_mathlib.sh

pdf:
	mkdir -p build/paper
	cd paper/source && for i in 1 2 3; do \
	  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=../../build/paper main.tex > /dev/null \
	  || { echo "pdflatex failed; see build/paper/main.log"; exit 1; }; done
	@echo "PDF: build/paper/main.pdf"

clean:
	rm -rf build
