.PHONY: clean talk.pdf

#PODMAN=podman run -i --rm --name latex -v "${PWD}":/usr/src/app:z -w /usr/src/app registry.gitlab.com/islandoftex/images/texlive:TL2024-historic
LATEXMK=$(PODMAN) latexmk -shell-escape -pdflatex=lualatex -pdf -auxdir=aux

talk.pdf:
	${LATEXMK} talk

clean:
	rm -rf aux talk.pdf
