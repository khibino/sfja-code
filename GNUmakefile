
%.vo: %.v
	coqc $<

sources = \
	Basics.v \
	Lists.v

objs = $(sources:.v=.vo)

targets = $(objs)

all: $(targets)

clean:
	$(RM) $(objs)
