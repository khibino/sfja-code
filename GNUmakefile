
%.vo %.glob: %.v
	coqc $<

sources = \
	OmegaCompat.v	\
	Basics.v	\
	Lists.v		\
	Poly.v		\
	Gen.v		\
	Props.v		\
	Logic.v         \
	SfLib.v         \
	Imp.v           \
	Equiv.v         \
	ImpList.v       \
	Rel.v           \
	Smallstep.v     \
	Types.v         \
	Stlc.v          \
	MoreStlc.v


objs = $(sources:.v=.vo)
globs = $(sources:.v=.glob)

targets = $(objs)

all: $(targets)

OmegaCompat.v:
	./gen-omega-compat.sh > $@

clean:
	$(RM) OmegaCompat.v
	$(RM) $(objs)
	$(RM) $(globs)
