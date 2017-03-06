
%.vo %.glob: %.v
	coqc $<

sources = \
	Basics.v	\
	Lists.v		\
	Poly.v		\
	Gen.v		\
	Prop.v		\
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

clean:
	$(RM) $(objs)
	$(RM) $(globs)
