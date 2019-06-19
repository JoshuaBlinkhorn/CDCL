CC=gcc
Flags=-Wall -Wpedantic

all: executable
	
debug: Flags += -DDEBUG
debug: objects
debug: executable

	
executable: objects CDCL.h
	$(CC) $(Flags) -o CDCL main.o CDCL.o

objects :
	$(CC) $(Flags) -c main.c CDCL.c

clean:
	rm -f CDCL main.o CDCL.o
