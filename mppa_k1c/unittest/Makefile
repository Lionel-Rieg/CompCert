# Needs to be called from CompCert root directory
# $ make -f mppa_k1c/unittest/Makefile postpass_test

include Makefile.extr

TEST_CMX=mppa_k1c/unittest/postpass_test.cmx

UNITTEST_OBJS:=$(shell $(MODORDER) $(TEST_CMX))

postpass_test: $(TEST_CMX) $(UNITTEST_OBJS)
	@echo "Linking $@"
	@$(OCAMLOPT) -o $@ $(LIBS) $(LINK_OPT) $+
