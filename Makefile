#
# Makefile for the malloc lab
#

CC = gcc
#CC = gcc-13 # for local mac execution/debugging

# Change this to -O0 (big-Oh, numeral zero) if you need to use a debugger on your code
COPT = -O3
#COPT = -O0 # for local mac execution/debugging
CFLAGS = -Wall -Wextra -Werror $(COPT) -g -DDRIVER -Wno-unused-function -Wno-unused-parameter
#CFLAGS = -Wall -Wextra $(COPT) -g -DDRIVER # for local mac execution/debugging
LIBS = -lm

COBJS = memlib.o fcyc.o clock.o stree.o
NOBJS = mdriver.o mm.o $(COBJS)

#MM = mm_squish.c
MM = mm_slabs.c

all: mdriver

# Regular driver
mdriver: $(NOBJS)
	$(CC) $(CFLAGS) -o mdriver $(NOBJS) $(LIBS)

mm.o: $(MM) mm.h memlib.h $(MC)
	$(CC) $(CFLAGS) -c $(MM) -o mm.o

mdriver.o: mdriver.c fcyc.h clock.h memlib.h config.h mm.h stree.h
memlib.o: memlib.c memlib.h
mm.o: $(MM) mm.h memlib.h
fcyc.o: fcyc.c fcyc.h
ftimer.o: ftimer.c ftimer.h config.h
clock.o: clock.c clock.h
stree.o: stree.c stree.h

clean:
	rm -f *~ *.o mdriver

handin:
	@echo 'Commit your mm.c file into your GitHub repo.'
