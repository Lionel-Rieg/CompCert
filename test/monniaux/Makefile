# NOTE: do NOT run this makefile with the -j option

CCOMP?=ccomp

#all: compile_times.pdf measure_times.k1c.pdf
all: measures.csv

verifier_times.txt: Asmblockdeps.patch
	(cd ../../ && make -j20)
	patch $(realpath ../../extraction/Asmblockdeps.ml) < $<
	(cd ../../ && make -j20); patch -R $(realpath ../../extraction/Asmblockdeps.ml) < $<
	bash clean_benches.sh
	bash build_benches.sh $@

oracle_times.txt: PostpassSchedulingOracle.patch
	(cd ../../ && make -j20)
	patch $(realpath ../../mppa_k1c/PostpassSchedulingOracle.ml) < $<
	(cd ../../ && make -j20); patch -R $(realpath ../../mppa_k1c/PostpassSchedulingOracle.ml) < $<
	bash clean_benches.sh
	bash build_benches.sh $@

measures.csv:
	(cd ../../ && make -j20 && make install)
	bash build_benches.sh
	bash run_benches.sh $@

#compile_times.pdf: gencompile.py verifier_times.txt oracle_times.txt
#	python3.5 $^ $@
#
#measure_times.k1c.pdf: gengraphs.py measures.csv
#	python3.5 $^ $(basename $(basename $@))

.PHONY:
clean:
	rm -f verifier_times.txt oracle_times.txt compile_times.pdf measure_times.k1c.pdf measures.csv
