# Needs to be called from CompCert root directory
# $ make -f kvx/unittest/Makefile postpass_test

include Makefile.extr

TEST_CMX=kvx/unittest/postpass_test.cmx

UNITTEST_OBJS:=$(shell $(MODORDER) $(TEST_CMX))

postpass_test: $(UNITTEST_OBJS)
	@echo "Linking $@ $(UNITTEST_OBJS)"
	@$(OCAMLOPT) -o $@ $(LIBS) $(LINK_OPT) $+

