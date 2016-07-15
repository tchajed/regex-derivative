regex.vo: regex.v
	coqc -q $<

regex.ml: regex.vo Extract.v
	coqc -q Extract.v

.PHONY: clean

clean:
	rm -f *.vo *.glob regex.ml regex.mli
