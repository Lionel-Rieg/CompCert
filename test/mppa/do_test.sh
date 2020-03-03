do_test () {
cat << EOF

##
# PRNG tests
##
EOF
(cd prng && make $1 -j$2)

cat << EOF

##
# Matrix Multiplication tests
##
EOF
(cd mmult && make $1 -j$2)

cat << EOF

##
# List sort tests
##
EOF
(cd sort && make $1 -j$2)

cat << EOF

##
# Instruction unit tests
##
EOF
(cd instr && make $1 -j$2)

cat << EOF

##
# Interoperability with GCC
##
EOF
(cd interop && make $1 -j$2)

cat << EOF

##
# printf wrapper test
##
(cd lib && make $1 -j$2)
EOF

}
