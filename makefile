DIRS = aqt num qip oqs lie tqi gr

.PHONY: clean

clean:
	find . -type f \( -name "*.log" -o -name "*.out" -o -name "*.fls" -o -name "*.aux" -o -name "*.fdb_latexmk" -o -name "*.synctex.gz" -o -name "*.bbl" -o -name "*.bcf" -o -name "*.blg" -o -name "*.toc" -o -name "*.run.xml" \) -delete

build:
	for dir in $(DIRS); do \
		pushd $$dir; \
		latexmk -pdf -quiet; \
		popd; \
	done