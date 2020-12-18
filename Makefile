PROG= gitup
SRCS= gitup.c

LDADD= -lssl -lz -lcrypto -lprivateucl

WARNS= 6

MAN= gitup.1 gitup.conf.5

.include <bsd.prog.mk>

