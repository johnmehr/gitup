CC = cc
CFLAGS = -O2 -g
LDFLAGS = -lssl -lcrypto -lz
COMPILE = $(CC) $(CFLAGS)

gitup: gitup.c 
	$(COMPILE) -o $@ $< $(LDFLAGS)

