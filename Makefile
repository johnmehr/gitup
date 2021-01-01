PROG= gitup
SRCS= gitup.c

.if !empty(OPENSSLINC)
CFLAGS+=	-I${OPENSSLINC}
.endif

.if !empty(OPENSSLLIB)
LDFLAGS+=	-L${OPENSSLLIB}
.endif

.if empty(CONFIG_FILE_PATH)
CONFIG_FILE_PATH=	/usr/local/etc/gitup.conf
.endif

CFLAGS+=	-DCONFIG_FILE_PATH=\"${CONFIG_FILE_PATH}\"

LDADD= -lssl -lz -lcrypto -lprivateucl

WARNS= 6

MAN= gitup.1 gitup.conf.5
CLEANFILES+= gitup.1 gitup.conf.5

gitup.1: gitup.1.in
	sed -e "s,%%CONFIG_FILE_PATH%%,${CONFIG_FILE_PATH},g" \
		gitup.1.in > gitup.1

gitup.conf.5: gitup.conf.5.in
	sed -e "s,%%CONFIG_FILE_PATH%%,${CONFIG_FILE_PATH},g" \
		gitup.conf.5.in > gitup.conf.5

.include <bsd.prog.mk>

