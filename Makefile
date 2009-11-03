HC      = ghc
HC_OPTS = $(EXTRA_HC_OPTS)

SRCS = Rewrite/Helpers.lhs Rewrite/PreTransform.lhs Rewrite/Unify.lhs Rewrite/Families.lhs Rewrite/Synonyms.lhs ConstraintTermsPrototype.lhs

OBJS = Rewrite/Helpers.o Rewrite/PreTransform.o Rewrite/Unify.o Rewrite/Families.o Rewrite/Synonyms.o ConstraintTermsPrototype.o

.SUFFIXES : .o .hi .lhs .hc .s

constraintTerms : $(OBJS)
	$(HC) $(HC_OPTS) $(SRCS) -o constraintTermExts --make


# Standard suffix rules
.o.hi:
	@:

.lhs.o:
	$(HC) --make -c $< $(HC_OPTS)

.hs.o:
	$(HC) --make -c $< $(HC_OPTS)

clean:
	rm *.o
	rm *.hi
	rm Rewrite/*.o
	rm Rewrite/*.hi

