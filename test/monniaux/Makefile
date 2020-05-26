# NOTE: do NOT run this makefile with the -j option

CCOMP?=ccomp

#all: verifier_times.txt oracle_times.txt measures.csv
all: measures.csv

verifier_times.txt: Asmblockdeps.patch
	(cd ../../ && make -j20 && make install)
	patch $(realpath ../../extraction/Asmblockdeps.ml) < $<
	(cd ../../ && make -j20 && make install); patch -R $(realpath ../../extraction/Asmblockdeps.ml) < $<
	bash clean_benches.sh
	bash build_benches.sh $@

oracle_times.txt: PostpassSchedulingOracle.patch
	(cd ../../ && make -j20 && make install)
	patch $(realpath ../../kvx/PostpassSchedulingOracle.ml) < $<
	(cd ../../ && make -j20 && make install); patch -R $(realpath ../../kvx/PostpassSchedulingOracle.ml) < $<
	bash clean_benches.sh
	bash build_benches.sh $@

measures.csv:
	@echo "Building compcert.."
	@(cd ../../ && make -s -j20 && make -s install)
	@echo "Building benches..."
	@bash build_benches.sh
	@echo "Benches built. Running benches..."
	@bash run_benches.sh $@

#compile_times.pdf: gencompile.py verifier_times.txt oracle_times.txt
#	python3.5 $^ $@
#
#measure_times.kvx.pdf: gengraphs.py measures.csv
#	python3.5 $^ $(basename $(basename $@))

.PHONY:
clean:
	@bash clean_benches.sh
	rm -f verifier_times.txt oracle_times.txt compile_times.pdf measure_times.kvx.pdf measures.csv
