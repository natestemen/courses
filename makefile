.PHONY: clean

clean:
	find . -type f \( -name "*.log" -o -name "*.out" -o -name "*.fls" -o -name "*.aux" -o -name "*.fdb_latexmk" -o -name "*.synctex.gz" \) -delete