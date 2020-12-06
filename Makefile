CC := clang
CFLAGS = -O2 -g
LDFLAGS = -lssl -lcrypto -lz
COMPILE = $(CC) $(CFLAGS) -DGITUPCONF='"$(GITUPCONF)"'
SED = sed
GITUPCONF = /usr/local/etc/gitup.conf

all: gitup gitup.1 gitup.conf.5

gitup: gitup.c 
	$(COMPILE) -o $@ $< $(LDFLAGS)

gitup.1: gitup.1.in
	$(SED) 's,GITUPCONF,$(GITUPCONF),g' $> > $@

gitup.conf.5: gitup.conf.5.in
	$(SED) 's,GITUPCONF,$(GITUPCONF),g' $> > $@
