default:
	pdflatex -shell-escape main-concur2026.tex

bib:
	bibtex main-concur2026

final:
	pdflatex -shell-escape main-concur2026.tex
	bibtex main-concur2026
	pdflatex -shell-escape main-concur2026.tex
	pdflatex -shell-escape main-concur2026.tex


add:
	git add Makefile *tex *sty main.bib

clean:
	rm -rf *.aux *.bbl *.blg *.log *.out *~ *bak *vtc *nix *lock _minted*
