DAFNY = dafny
FLAGS = /noCheating:1 /timeLimit:120 /trace

.PHONY = clean

all: singleRP.dll

%.dll: %.dfy
	$(DAFNY) $(FLAGS) $<

clean:
	rm -rf *.dll *.dll.mdb
