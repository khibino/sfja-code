
%.vo %.glob: %.v
	coqc $<

sources = \
	Basics.v   \
	Lists.v    \
	Poly.v     \

objs = $(sources:.v=.vo)
globs = $(sources:.v=.glob)

targets = $(objs)

all: $(targets)

clean:
	$(RM) $(objs)
	$(RM) $(globs)
