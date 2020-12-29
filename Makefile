PROG= gitup
SRCS= gitup.c

.if !empty(OPENSSLINC)
CFLAGS+=	-I${OPENSSLINC}
.endif

.if !empty(OPENSSLLIB)
LDFLAGS+=	-L${OPENSSLLIB}
.endif

LDADD= -lssl -lz -lcrypto -lprivateucl

WARNS= 6

MAN= gitup.1 gitup.conf.5

.include <bsd.prog.mk>

