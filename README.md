# gitup
A minimalist FreeBSD program to clone/pull Git repositories.  

Intended for non-developers, [gitup(1)](https://man.freebsd.org/cgi/man.cgi?query=gitup&sektion=1&manpath=freebsd-ports) synchronizes local repositories – without the complexities of the official Git client, [git(1)](https://git-scm.com/docs/git).  

## Requirements and compatibility

Minimalism: 

* [no dependencies](https://www.freshports.org/net/gitup/#dependencies)
* gitup does **not** use special files, such as the object database, that may be found in [a `.git` subdirectory](https://git-scm.com/docs/git#_discussion). 

For integrity of data and metadata: 

* if a working directory includes a `.git` subdirectory, a `gitup` command will not proceed
* if a working directory is non-empty and lacks a `.git` subdirectory, `git` will not proceed.

## Scope

gitup was originally designed to work with `/usr/ports` and `/usr/src` directories – for the _ports_ and _src_ source code trees of [the FreeBSD Project](https://www.freebsd.org/).

Other working directories, not necessarily related to FreeBSD, may be configured as described in [gitup.conf(5)](https://man.freebsd.org/cgi/man.cgi?query=gitup.conf&sektion=5&manpath=freebsd-ports).
