# NOTE: do NOT run this makefile with the -j option

CCOMP?=ccomp

all: compile_times.pdf

verifier_times.txt: Asmblockdeps.patch
	patch ../../extraction/Asmblockdeps.ml < $<
	(cd ../../ && make -j20 && make install); patch -R ../../extraction/Asmblockdeps.ml < $<
	bash clean_benches.sh
	bash build_benches.sh $@

oracle_times.txt: PostpassSchedulingOracle.patch
	patch ../../mppa_k1c/PostpassSchedulingOracle.ml < $<
	(cd ../../ && make -j20 && make install); patch -R ../../mppa_k1c/PostpassSchedulingOracle.ml < $<
	bash clean_benches.sh
	bash build_benches.sh $@

compile_times.pdf: gencompile.py verifier_times.txt oracle_times.txt
	python3.6 $^ $@

.PHONY:
clean:
	rm -f verifier_times.txt oracle_times.txt compile_times.pdf
