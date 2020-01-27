regex.vo: regex.v
	coqc -q $<

regex.ml: regex.vo Extract.v
	coqc -q Extract.v

all: regex.vo regex.ml

.PHONY: clean all

clean:
	rm -f *.vo *.glob regex.ml regex.mli
