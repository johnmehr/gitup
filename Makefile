PROG= gitup
SRCS= gitup.c

.if empty(CONFIG_FILE_PATH)
CONFIG_FILE_PATH=	/usr/local/etc/gitup.conf
.endif

CFLAGS+=	-DCONFIG_FILE_PATH=\"${CONFIG_FILE_PATH}\"
LDADD= -lssl -lz -lcrypto -lprivateucl

WARNS= 6

MAN= gitup.1 gitup.conf.5

.include <bsd.prog.mk>

