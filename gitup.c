/*-
 * Copyright (c) 2012-2021, John Mehr <jmehr@umn.edu>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * $FreeBSD$
 */

#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/tree.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <openssl/sha.h>
#include <openssl/ssl.h>
#include <openssl/ssl3.h>
#include <openssl/err.h>
#include <private/ucl/ucl.h>

#include <ctype.h>
#include <dirent.h>
#include <err.h>
#include <errno.h>
#include <fcntl.h>
#include <netdb.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <zlib.h>

#define	GITUP_VERSION     "0.90"
#define	BUFFER_UNIT_SMALL  4096
#define	BUFFER_UNIT_LARGE  1048576

#ifndef CONFIG_FILE_PATH
#define CONFIG_FILE_PATH "./gitup.conf"
#endif

struct object_node {
	RB_ENTRY(object_node) link;
	char     *hash;
	uint8_t   type;
	uint32_t  index;
	uint32_t  index_delta;
	char     *ref_delta_hash;
	uint32_t  pack_offset;
	char     *buffer;
	uint32_t  buffer_size;
};

struct file_node {
	RB_ENTRY(file_node) link_hash;
	RB_ENTRY(file_node) link_path;
	mode_t  mode;
	char   *hash;
	char   *path;
	bool    keep;
	bool    save;
	bool    new;
};

typedef struct {
	SSL                 *ssl;
	SSL_CTX             *ctx;
	int                  socket_descriptor;
	char                *host;
	uint16_t             port;
	char                *agent;
	char                *section;
	char                *repository;
	char                *branch;
	char                *tag;
	char                *have;
	char                *want;
	char                *response;
	int                  response_blocks;
	uint32_t             response_size;
	bool                 clone;
	bool                 repair;
	struct object_node **object;
	int                  objects;
	char                *pack_file;
	char                *path_target;
	char                *path_work;
	char                *remote_files;
	char               **ignore;
	int                  ignores;
	bool                 keep_pack_file;
	bool                 use_pack_file;
	int                  verbosity;
} connector;

static void     append_string(char **, unsigned int *, unsigned int *, const char *, int);
static void     apply_deltas(connector *);
static char *   calculate_file_hash(char *, int);
static char *   calculate_object_hash(char *, uint32_t, int);
static void     extract_tree_item(struct file_node *, char **);
static void     fetch_pack(connector *, char *);
static int      file_node_compare_hash(const struct file_node *, const struct file_node *);
static int      file_node_compare_path(const struct file_node *, const struct file_node *);
static void     file_node_free(struct file_node *);
static void     find_local_tree(connector *, char *);
static void     get_commit_details(connector *);
static char *   illegible_hash(char *);
static char *   build_clone_command(connector *);
static char *   build_pull_command(connector *);
static char *   build_repair_command(connector *);
static char *   legible_hash(char *);
static int      load_configuration(connector *, const char *, char **, int);
static void     load_file(const char *, char **, uint32_t *);
static void     load_object(connector *, char *, char *);
static void     load_pack(connector *);
static void     load_remote_file_list(connector *);
static int      object_node_compare(const struct object_node *, const struct object_node *);
static void     object_node_free(struct object_node *);
static void     process_command(connector *, char *);
static void     process_tree(connector *, int, char *, char *);
static void     prune_tree(connector *, char *);
static void     save_file(char *, int, char *, int, int verbosity, bool);
static void     save_objects(connector *);
static void     save_repairs(connector *);
static void     send_command(connector *, char *);
static void     ssl_connect(connector *);
static void     store_object(connector *, int, char *, int, int, int, char *);
static uint32_t unpack_delta_integer(char *, uint32_t *, int);
static void     unpack_objects(connector *);
static uint32_t unpack_variable_length_integer(char *, uint32_t *);
static void     usage(const char *);

/*
 * node_compare
 *
 * Functions that instruct the red-black trees how to sort keys.
 */

static int
file_node_compare_path(const struct file_node *a, const struct file_node *b)
{
	return (strcmp(a->path, b->path));
}


static int
file_node_compare_hash(const struct file_node *a, const struct file_node *b)
{
	return (strcmp(a->hash, b->hash));
}


static int
object_node_compare(const struct object_node *a, const struct object_node *b)
{
	return (strcmp(a->hash, b->hash));
}


/*
 * node_free
 *
 * Functions that free the memory used by tree nodes.
 */

static void
file_node_free(struct file_node *node)
{
	free(node->hash);
	free(node->path);
	free(node);
}


static void
object_node_free(struct object_node *node)
{
	free(node->hash);
	free(node->ref_delta_hash);
	free(node->buffer);
	free(node);
}


static RB_HEAD(Tree_Remote_Path, file_node) Remote_Path = RB_INITIALIZER(&Remote_Path);
RB_PROTOTYPE(Tree_Remote_Path, file_node, link_path, file_node_compare_path)
RB_GENERATE(Tree_Remote_Path,  file_node, link_path, file_node_compare_path)

static RB_HEAD(Tree_Local_Path, file_node) Local_Path = RB_INITIALIZER(&Local_Path);
RB_PROTOTYPE(Tree_Local_Path, file_node, link_path, file_node_compare_path)
RB_GENERATE(Tree_Local_Path,  file_node, link_path, file_node_compare_path)

static RB_HEAD(Tree_Local_Hash, file_node) Local_Hash = RB_INITIALIZER(&Local_Hash);
RB_PROTOTYPE(Tree_Local_Hash, file_node, link_hash, file_node_compare_hash)
RB_GENERATE(Tree_Local_Hash,  file_node, link_hash, file_node_compare_hash)

static RB_HEAD(Tree_Objects, object_node) Objects = RB_INITIALIZER(&Objects);
RB_PROTOTYPE(Tree_Objects, object_node, link, object_node_compare)
RB_GENERATE(Tree_Objects,  object_node, link, object_node_compare)


/*
 * legible_hash
 *
 * Function that converts a 20 byte binary SHA checksum into a 40 byte human-readable SHA checksum.
 */

static char *
legible_hash(char *hash_buffer)
{
	char *hash = NULL;
	int   x = 0;

	if ((hash = (char *)malloc(41)) == NULL)
		err(EXIT_FAILURE, "legible_hash: malloc");

	for (x = 0; x < 20; x++)
		snprintf(&hash[x * 2], 3, "%02x", (unsigned char)hash_buffer[x]);

	hash[40] = '\0';

	return (hash);
}


/*
 * illegible_hash
 *
 * Function that converts a 40 byte human-readable SHA checksum into a 20 byte binary SHA checksum.
 */

static char *
illegible_hash(char *hash_buffer)
{
	char *hash = NULL;
	int   x = 0;

	if ((hash = (char *)malloc(20)) == NULL)
		err(EXIT_FAILURE, "illegible_hash: malloc");

	for (x = 0; x < 20; x++)
		hash[x] = 16 * ((unsigned char)hash_buffer[x * 2] - (hash_buffer[x * 2] > 58 ? 87 : 48)) + (unsigned char)hash_buffer[x * 2 + 1] - (hash_buffer[x * 2 + 1] > 58 ? 87 : 48);

	return (hash);
}


/*
 * prune_tree
 *
 * Procedure that recursively removes a directory.
 */

static void
prune_tree(connector *connection, char *base_path)
{
	DIR           *directory = NULL;
	struct dirent *entry = NULL;
	char           full_path[strlen(base_path) + MAXNAMLEN + 1];
	int            file_name_size = 0;

	/* Sanity check the directory to prune. */

	if (strnstr(base_path, connection->path_target, strlen(connection->path_target)) != base_path)
		errc(EXIT_FAILURE, EACCES, "prune_tree: %s is not located in the %s tree", base_path, connection->path_target);

	if (strnstr(base_path, "../", strlen(base_path)) != NULL)
		errc(EXIT_FAILURE, EACCES, "prune_tree: illegal path traverse in %s", base_path);

	/* Remove the directory contents. */

	if ((directory = opendir(base_path)) != NULL) {
		while ((entry = readdir(directory)) != NULL) {
			file_name_size = strlen(entry->d_name);

			if ((file_name_size == 1) && (strcmp(entry->d_name, "." ) == 0))
				continue;

			if ((file_name_size == 2) && (strcmp(entry->d_name, "..") == 0))
				continue;

			snprintf(full_path, sizeof(full_path), "%s/%s", base_path, entry->d_name);

			if (entry->d_type == DT_DIR) {
				prune_tree(connection, full_path);
			} else {
				if ((remove(full_path) != 0) && (errno != ENOENT))
					err(EXIT_FAILURE, "prune_tree: cannot remove %s", full_path);
			}
		}

		closedir(directory);

		if (rmdir(base_path) != 0)
			err(EXIT_FAILURE, "prune_tree: cannot remove %s", base_path);
	}
}


/*
 * load_file
 *
 * Procedure that loads a local file into the specified buffer.
 */

static void
load_file(const char *path, char **buffer, uint32_t *buffer_size)
{
	struct stat file;
	int         fd;

	if (stat(path, &file) == -1)
		err(EXIT_FAILURE, "load_file: cannot find %s", path);

	if (file.st_size > 0) {
		if (file.st_size > *buffer_size) {
			*buffer_size = file.st_size;

			if ((*buffer = (char *)realloc(*buffer, *buffer_size + 1)) == NULL)
				err(EXIT_FAILURE, "load_file: malloc");
		}

		if ((fd = open(path, O_RDONLY)) == -1)
			err(EXIT_FAILURE, "load_file: cannot read %s", path);

		if ((uint32_t)read(fd, *buffer, *buffer_size) != *buffer_size)
			err(EXIT_FAILURE, "load_file: problem reading %s", path);

		close(fd);

		*(*buffer + *buffer_size) = '\0';
	}
}


/*
 * save_file
 *
 * Procedure that saves a blob/file.
 */

static void
save_file(char *path, int mode, char *buffer, int buffer_size, int verbosity, bool new)
{
	struct stat file;
	char        temp_buffer[buffer_size + 1];
	int         fd;

	if (verbosity > 0)
		printf(" %c %s\n", (new == true ? '+' : '*'), path);

	if (S_ISLNK(mode)) {
		/* Make sure the buffer is null terminated, then save it as the file to link to. */

		memcpy(temp_buffer, buffer, buffer_size);
		temp_buffer[buffer_size] = '\0';

		if (symlink(temp_buffer, path) == -1)
			err(EXIT_FAILURE, "save_file: symlink failure %s -> %s", path, temp_buffer);
	} else {
		/* If the file exists, make sure the permissions are intact. */

		if (stat(path, &file) == 0)
			chmod(path, mode);

		if (((fd = open(path, O_WRONLY | O_CREAT | O_TRUNC)) == -1) && (errno != EEXIST))
			err(EXIT_FAILURE, "save_file: write file failure %s", path);

		chmod(path, mode);
		write(fd, buffer, buffer_size);
		close(fd);
	}
}


/*
 * calculate_object_hash
 *
 * Function that adds Git's "type file-size\0" header to a buffer and returns the SHA checksum.
 */

static char *
calculate_object_hash(char *buffer, uint32_t buffer_size, int type)
{
	int         digits = buffer_size, header_width = 0;
	char       *hash = NULL, *hash_buffer = NULL, *temp_buffer = NULL;
	const char *types[8] = { "", "commit", "tree", "blob", "tag", "", "ofs-delta", "ref-delta" };

	if ((hash_buffer = (char *)malloc(20)) == NULL)
		err(EXIT_FAILURE, "calculate_object_hash: malloc");

	if ((temp_buffer = (char *)malloc(buffer_size + 24)) == NULL)
		err(EXIT_FAILURE, "calculate_object_hash: malloc");

	/* Start with the git "type file-size\0" header. */

	header_width = strlen(types[type]) + 3;

	while ((digits /= 10) > 0)
		header_width++;

	snprintf(temp_buffer, header_width, "%s %u", types[type], buffer_size);

	/* Then add the buffer. */

	memcpy(temp_buffer + header_width, buffer, buffer_size);

	/* Calculate the SHA checksum. */

	SHA1((unsigned char *)temp_buffer, buffer_size + header_width, (unsigned char *)hash_buffer);

	hash = legible_hash(hash_buffer);

	free(hash_buffer);
	free(temp_buffer);

	return (hash);
}


/*
 * calculate_file_hash
 *
 * Function that loads a local file and returns the SHA checksum.
 */

static char *
calculate_file_hash(char *path, int file_mode)
{
	char     *buffer = NULL, *hash = NULL, temp_path[BUFFER_UNIT_SMALL];
	uint32_t  buffer_size = 0, bytes_read = 0;

	if (S_ISLNK(file_mode)) {
		bytes_read = readlink(path, temp_path, BUFFER_UNIT_SMALL);
		temp_path[bytes_read] = '\0';

		hash = calculate_object_hash(temp_path, strlen(temp_path), 3);
	} else {
		load_file(path, &buffer, &buffer_size);
		hash = calculate_object_hash(buffer, buffer_size, 3);
		free(buffer);
	}

	return (hash);
}


/*
 * append_string
 *
 * Procedure that appends one string to another.
 */

static void
append_string(char **buffer, unsigned int *buffer_size, unsigned int *string_length, const char *addendum, int addendum_size)
{
	int adjust = 0;

	while (*string_length + addendum_size > *buffer_size) {
		adjust = 1;
		*buffer_size += BUFFER_UNIT_SMALL;
	}

	if ((adjust) && ((*buffer = (char *)realloc(*buffer, *buffer_size + 1)) == NULL))
		err(EXIT_FAILURE, "append_string: realloc");

	memcpy(*buffer + *string_length, addendum, addendum_size);

	*string_length += addendum_size;

	*(*buffer + *string_length) = '\0';
}


/*
 * load_remote_file_list
 *
 * Procedure that loads the list of remote files and checksums, if it exists.
 */

static void
load_remote_file_list(connector *connection)
{
	struct file_node *file = NULL;
	char             *line = NULL, *hash = NULL, *path = NULL, *remote_files = NULL;
	char              temp[BUFFER_UNIT_SMALL], base_path[BUFFER_UNIT_SMALL], *buffer = NULL, *temp_hash = NULL;
	uint32_t          count = 0, remote_file_size = 0, buffer_size = 0, buffer_length = 0;

	load_file(connection->remote_files, &remote_files, &remote_file_size);

	while ((line = strsep(&remote_files, "\n"))) {
		/* The first line stores the "have". */

		if (count++ == 0) {
			connection->have = strdup(line);
			continue;
		}

		/* Empty lines signify the end of a directory entry, so create an
		   obj_tree for what has been read. */

		if (strlen(line) == 0) {
			if (buffer != NULL) {
				if (connection->clone == false)
					store_object(connection, 2, buffer, buffer_length, 0, 0, NULL);

				buffer = NULL;
				buffer_size = buffer_length = 0;
			}

			continue;
		}

		/* Split the line and save the data into the remote files tree. */

		hash = strchr(line, '\t') + 1;
		path = strchr(hash, '\t') + 1;

		*(hash -  1) = '\0';
		*(hash + 40) = '\0';

		if ((file = (struct file_node *)malloc(sizeof(struct file_node))) == NULL)
			err(EXIT_FAILURE, "load_remote_file_list: malloc");

		file->mode = strtol(line, (char **)NULL, 8);
		file->hash = strdup(hash);
		file->save = 0;

		if (path[strlen(path) - 1] == '/') {
			snprintf(base_path, sizeof(base_path), "%s", path);
			snprintf(temp, sizeof(temp), "%s", path);
			temp[strlen(path) - 1] = '\0';
		} else {
			snprintf(temp, sizeof(temp), "%s%s", base_path, path);

			/* Add the line to the buffer that will become the obj_tree for this directory. */

			temp_hash = illegible_hash(hash);

			append_string(&buffer, &buffer_size, &buffer_length, line, strlen(line));
			append_string(&buffer, &buffer_size, &buffer_length, " ", 1);
			append_string(&buffer, &buffer_size, &buffer_length, path, strlen(path));
			append_string(&buffer, &buffer_size, &buffer_length, "\0", 1);
			append_string(&buffer, &buffer_size, &buffer_length, temp_hash, 20);

			free(temp_hash);
		}

		file->path = strdup(temp);

		RB_INSERT(Tree_Remote_Path, &Remote_Path, file);
	}

	free(remote_files);
}


/*
 * find_local_tree
 *
 * Procedure that recursively finds and adds local files and directories to
 * separate red-black trees.
 */

static void
find_local_tree(connector *connection, char *base_path)
{
	DIR              *directory = NULL;
	struct stat       file;
	struct dirent    *entry = NULL;
	struct file_node *new_node = NULL, find, *found = NULL;
	char             *full_path = NULL;
	int               file_name_size = 0, full_path_size = 0;

	/* Make sure the base path exists in the remote files list. */

	find.path = base_path;
	found     = RB_FIND(Tree_Remote_Path, &Remote_Path, &find);

	/* Add the base path to the local trees. */

	if ((new_node = (struct file_node *)malloc(sizeof(struct file_node))) == NULL)
		err(EXIT_FAILURE, "find_local_tree: malloc");

	new_node->mode = (found ? found->mode : 040000);
	new_node->hash = (found ? strdup(found->hash) : NULL);
	new_node->path = strdup(base_path);
	new_node->keep = (strlen(base_path) == strlen(connection->path_target) ? true : false);
	new_node->save = false;
	new_node->new  = false;

	RB_INSERT(Tree_Local_Path, &Local_Path, new_node);

	if (found)
		RB_INSERT(Tree_Local_Hash, &Local_Hash, new_node);

	/* Process the directory's contents. */

	if ((stat(base_path, &file) != -1) && ((directory = opendir(base_path)) != NULL)) {
		while ((entry = readdir(directory)) != NULL) {
			file_name_size = strlen(entry->d_name);

			if ((file_name_size == 1) && (strcmp(entry->d_name, "." ) == 0))
				continue;

			if ((file_name_size == 2) && (strcmp(entry->d_name, "..") == 0))
				continue;

			if ((file_name_size == 4) && (strcmp(entry->d_name, ".git") == 0)) {
				fprintf(stderr, " ! A .git directory was found -- gitup does not update this directory which will cause problems for the official Git client.\n");
				fprintf(stderr, " ! If you wish to use gitup, please remove %s/%s and rerun gitup.\n", base_path, entry->d_name);
				exit(EXIT_FAILURE);
				}

			full_path_size = strlen(base_path) + strlen(entry->d_name) + 2;

			if ((full_path = (char *)malloc(full_path_size + 1)) == NULL)
				err(EXIT_FAILURE, "find_local_tree: full_path malloc");

			snprintf(full_path, full_path_size, "%s/%s", base_path, entry->d_name);

			if (lstat(full_path, &file) == -1)
				err(EXIT_FAILURE, "find_local_tree: %s", full_path);

			if (S_ISDIR(file.st_mode)) {
				find_local_tree(connection, full_path);
				free(full_path);
			} else {
				if ((new_node = (struct file_node *)malloc(sizeof(struct file_node))) == NULL)
					err(EXIT_FAILURE, "find_local_tree: malloc");

				new_node->mode = file.st_mode;
				new_node->hash = calculate_file_hash(full_path, file.st_mode);
				new_node->path = full_path;
				new_node->keep = (strnstr(full_path, ".gituprevision", strlen(full_path)) != NULL ? true : false);
				new_node->save = false;
				new_node->new  = false;

				RB_INSERT(Tree_Local_Hash, &Local_Hash, new_node);
				RB_INSERT(Tree_Local_Path, &Local_Path, new_node);
			}
		}

		closedir(directory);
	}
}


/*
 * load_object
 *
 * Procedure that loads a local file and adds it to the array/tree of pack file objects.
 */

static void
load_object(connector *connection, char *hash, char *path)
{
	struct object_node *object = NULL, lookup_object;
	struct file_node   *find = NULL, lookup_file;
	char               *buffer = NULL;
	uint32_t            buffer_size = 0;

	lookup_object.hash = hash;
	lookup_file.hash   = hash;
	lookup_file.path   = path;

	/* If the object doesn't exist, look for it first by hash, then by path and if
	   it is found and the SHA checksum references a file, load it and store it. */

	if ((object = RB_FIND(Tree_Objects, &Objects, &lookup_object)) == NULL) {
		if ((find = RB_FIND(Tree_Local_Hash, &Local_Hash, &lookup_file)) == NULL)
			find = RB_FIND(Tree_Local_Path, &Local_Path, &lookup_file);

		if (find) {
			if (!S_ISDIR(find->mode)) {
				load_file(find->path, &buffer, &buffer_size);
				store_object(connection, 3, buffer, buffer_size, 0, 0, NULL);
			}
		} else {
			errc(EXIT_FAILURE, ENOENT, "load_object: local file for object %s -- %s not found", hash, path);
		}
	}
}


/*
 * ssl_connect
 *
 * Procedure that (re)establishes a connection with the server.
 */

static void
ssl_connect(connector *connection)
{
	struct addrinfo hints, *start, *temp;
	struct timeval  timeout;
	int             error, option;
	char            type[10];

	if (connection->socket_descriptor)
		if (close(connection->socket_descriptor) != 0)
			if (errno != EBADF)
				err(EXIT_FAILURE, "ssl_connect: close_connection");

	snprintf(type, sizeof(type), "%d", connection->port);

	bzero(&hints, sizeof(struct addrinfo));
	hints.ai_family = AF_INET;
	hints.ai_socktype = SOCK_STREAM;

	if ((error = getaddrinfo(connection->host, type, &hints, &start)))
		errx(EXIT_FAILURE, "%s", gai_strerror(error));

	connection->socket_descriptor = -1;

	while (start) {
		temp = start;

		if (connection->socket_descriptor < 0) {
			if ((connection->socket_descriptor = socket(temp->ai_family, temp->ai_socktype, temp->ai_protocol)) < 0)
				err(EXIT_FAILURE, "ssl_connect: socket failure");

			if (connect(connection->socket_descriptor, temp->ai_addr, temp->ai_addrlen) < 0)
				err(EXIT_FAILURE, "ssl_connect: connect failure (%d)", errno);
		}

		start = temp->ai_next;
		freeaddrinfo(temp);
	}

	if (SSL_library_init() == 0)
		err(EXIT_FAILURE, "ssl_connect: SSL_library_init");

	SSL_load_error_strings();
	connection->ctx = SSL_CTX_new(SSLv23_client_method());
	SSL_CTX_set_mode(connection->ctx, SSL_MODE_AUTO_RETRY);
	SSL_CTX_set_options(connection->ctx, SSL_OP_ALL | SSL_OP_NO_TICKET);

	if ((connection->ssl = SSL_new(connection->ctx)) == NULL)
		err(EXIT_FAILURE, "ssl_connect: SSL_new");

	SSL_set_fd(connection->ssl, connection->socket_descriptor);

	while ((error = SSL_connect(connection->ssl)) == -1)
		fprintf(stderr, "ssl_connect: SSL_connect error: %d\n", SSL_get_error(connection->ssl, error));

	option = 1;

	if (setsockopt(connection->socket_descriptor, SOL_SOCKET, SO_KEEPALIVE, &option, sizeof(int)))
		err(EXIT_FAILURE, "ssl_connect: setsockopt SO_KEEPALIVE error");

	option = BUFFER_UNIT_LARGE;

	if (setsockopt(connection->socket_descriptor, SOL_SOCKET, SO_SNDBUF, &option, sizeof(int)))
		err(EXIT_FAILURE, "ssl_connect: setsockopt SO_SNDBUF error");

	if (setsockopt(connection->socket_descriptor, SOL_SOCKET, SO_RCVBUF, &option, sizeof(int)))
		err(EXIT_FAILURE, "ssl_connect: setsockopt SO_RCVBUF error");

	bzero(&timeout, sizeof(struct timeval));
	timeout.tv_sec = 300;

	if (setsockopt(connection->socket_descriptor, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof(struct timeval)))
		err(EXIT_FAILURE, "ssl_connect: setsockopt SO_RCVTIMEO error");

	if (setsockopt(connection->socket_descriptor, SOL_SOCKET, SO_SNDTIMEO, &timeout, sizeof(struct timeval)))
		err(EXIT_FAILURE, "ssl_connect: setsockopt SO_SNDTIMEO error");
}


/*
 * process_command
 *
 * Procedure that sends a command to the server and processes the response.
 */

static void
process_command(connector *connection, char *command)
{
	char  read_buffer[BUFFER_UNIT_SMALL];
	char *marker_start = NULL, *marker_end = NULL, *data_start = NULL;
	int   chunk_size = -1, bytes_expected = 0, marker_offset = 0, data_start_offset = 0;
	int   bytes_read = 0, total_bytes_read = 0, bytes_to_move = 0;
	int   bytes_sent = 0, total_bytes_sent = 0, check_bytes = 0;
	int   bytes_to_write = strlen(command), error = 0, twirl = 0;
	char  twirly[4] = { '|', '/', '-', '\\' };

	if (connection->verbosity > 1)
		fprintf(stderr, "%s\n\n", command);

	/* Transmit the command to the server. */

	ssl_connect(connection);

	while (total_bytes_sent < bytes_to_write) {
		bytes_sent = SSL_write(
			connection->ssl,
			command + total_bytes_sent,
			bytes_to_write - total_bytes_sent);

		if (bytes_sent <= 0) {
			if ((bytes_sent < 0) && ((errno == EINTR) || (errno == 0)))
				continue;
			else
				err(EXIT_FAILURE, "process_command: send command");
		}

		total_bytes_sent += bytes_sent;

		if (connection->verbosity > 1)
			fprintf(stderr, "\r==> bytes sent: %d", total_bytes_sent);
		}

	if (connection->verbosity > 1)
		fprintf(stderr, "\n");

	/* Process the response. */

	while (chunk_size) {
		bytes_read = SSL_read(connection->ssl, read_buffer, BUFFER_UNIT_SMALL);

		if (bytes_read == 0)
			break;

		if (bytes_read < 0)
			err(EXIT_FAILURE, "process_command: SSL_read error: %d", SSL_get_error(connection->ssl, error));

		/* Expand the buffer if needed, preserving the position and data_start if the buffer moves. */

		if (total_bytes_read + bytes_read > connection->response_blocks * BUFFER_UNIT_LARGE) {
			marker_offset     = marker_start - connection->response;
			data_start_offset = data_start   - connection->response;

			if ((connection->response = (char *)realloc(connection->response, ++connection->response_blocks * BUFFER_UNIT_LARGE)) == NULL)
				err(EXIT_FAILURE, "process_command: connection->response realloc");

			marker_start = connection->response + marker_offset;
			data_start   = connection->response + data_start_offset;
		}

		/* Add the bytes received to the buffer. */

		memcpy(connection->response + total_bytes_read, read_buffer, bytes_read + 1);
		total_bytes_read += bytes_read;
		connection->response[total_bytes_read] = '\0';

		if (connection->verbosity > 1)
			fprintf(stderr, "\r==> bytes read: %d\tbytes_expected: %d\ttotal_bytes_read: %d", bytes_read, bytes_expected, total_bytes_read);

		/* Find the boundary between the header and the data. */

		if (chunk_size == -1) {
			if ((marker_start = strnstr(connection->response, "\r\n\r\n", total_bytes_read)) == NULL) {
				continue;
			} else {
				bytes_expected = marker_start - connection->response + 4;
				marker_start += 2;
				data_start = marker_start;
			}
		}

		while (total_bytes_read + chunk_size > bytes_expected) {
			/* Make sure the whole chunk marker has been read. */

			check_bytes = total_bytes_read - (marker_start + 2 - connection->response);

			if (check_bytes < 0)
				break;

			marker_end = strnstr(marker_start + 2, "\r\n", check_bytes);

			if (marker_end == NULL)
				break;

			/* Remove the chunk length marker. */

			chunk_size    = strtol(marker_start, (char **)NULL, 16);
			bytes_to_move = total_bytes_read - (marker_end + 2 - connection->response) + 1;

			if (bytes_to_move < 0)
				break;

			memmove(marker_start, marker_end + 2, bytes_to_move);
			total_bytes_read -= (marker_end + 2 - marker_start);

			if (chunk_size == 0)
				break;

			marker_start += chunk_size;
			bytes_expected += chunk_size;

			if (connection->verbosity == 1)
				fprintf(stderr, "%c\r", twirly[twirl++ % 4]);
		}
	}

	if (connection->verbosity > 1)
		fprintf(stderr, "\n");

	if (strstr(connection->response, "HTTP/1.1 200 ") != connection->response)
		errc(EXIT_FAILURE, EINVAL, "process_command: read failure:\n%s\n", connection->response);

	/* Remove the header. */

	connection->response_size = total_bytes_read - (data_start - connection->response);
	memmove(connection->response, data_start, connection->response_size);
	connection->response[connection->response_size] = '\0';
}


/*
 * send_command
 *
 * Function that constructs the command to the fetch the full pack data.
 */

static void
send_command(connector *connection, char *want)
{
	char   *command = NULL;
	size_t  want_size = 0;

	want_size = strlen(want);

	if ((command = (char *)malloc(BUFFER_UNIT_SMALL + want_size)) == NULL)
		err(EXIT_FAILURE, "send_command: malloc");

	snprintf(command,
		BUFFER_UNIT_SMALL + want_size,
		"POST %s/git-upload-pack HTTP/1.1\r\n"
		"Host: %s:%d\r\n"
		"User-Agent: gitup/%s\r\n"
		"Accept-encoding: deflate, gzip\r\n"
		"Content-type: application/x-git-upload-pack-request\r\n"
		"Accept: application/x-git-upload-pack-result\r\n"
		"Git-Protocol: version=2\r\n"
		"Content-length: %zu\r\n"
		"\r\n"
		"%s",
		connection->repository,
		connection->host,
		connection->port,
		GITUP_VERSION,
		want_size,
		want);

	process_command(connection, command);

	free(command);
}


/*
 * build_clone_command
 *
 * Function that constructs and executes the command to the fetch the full pack data.
 */

static char *
build_clone_command(connector *connection)
{
	char    *command = NULL;
	uint8_t  agent_length = 0;

	agent_length = strlen(connection->agent) + 4;

	if ((command = (char *)malloc(BUFFER_UNIT_SMALL)) == NULL)
		err(EXIT_FAILURE, "build_clone_command: malloc");

	snprintf(command,
		BUFFER_UNIT_SMALL,
		"0011command=fetch"
		"%04x%s0001"
		"000fno-progress"
		"000dofs-delta"
		"0034shallow %s"
		"0032want %s\n"
		"0032want %s\n"
		"0009done\n0000",
		agent_length,
		connection->agent,
		connection->want,
		connection->want,
		connection->want);

	return (command);
}


/*
 * build_pull_command
 *
 * Function that constructs and executes the command to the fetch the incremental pack data.
 */

static char *
build_pull_command(connector *connection)
{
	char    *command = NULL;
	uint8_t  agent_length = 0;

	agent_length = strlen(connection->agent) + 4;

	if ((command = (char *)malloc(BUFFER_UNIT_SMALL)) == NULL)
		err(EXIT_FAILURE, "build_pull_command: malloc");

	snprintf(command,
		BUFFER_UNIT_SMALL,
		"0011command=fetch"
		"%04x%s0001"
		"000dthin-pack"
		"000fno-progress"
		"000dofs-delta"
		"0034shallow %s"
		"0034shallow %s"
		"000cdeepen 1"
		"0032want %s\n"
		"0032have %s\n"
		"0009done\n0000",
		agent_length,
		connection->agent,
		connection->want,
		connection->have,
		connection->want,
		connection->have);

	return (command);
}


/*
 * build_repair_command
 *
 * Procedure that compares the local repository tree with the data saved from the
 * last run to see if anything has been modified.
 */

static char *
build_repair_command(connector *connection)
{
	struct file_node *find = NULL, *found = NULL;
	char             *command = NULL, *want = NULL, line[BUFFER_UNIT_SMALL];
	uint32_t          want_size = 0, want_length = 0;
	uint8_t           agent_length = 0;

	agent_length = strlen(connection->agent) + 4;

	RB_FOREACH(find, Tree_Remote_Path, &Remote_Path) {
		found = RB_FIND(Tree_Local_Path, &Local_Path, find);

		if ((found == NULL) || (strncmp(found->hash, find->hash, 40) != 0)) {
			if (connection->verbosity)
				fprintf(stderr, " ! %s %s\n", find->path, (found == NULL ? "is missing." : "has been modified."));

			snprintf(line, sizeof(line), "0032want %s\n", find->hash);
			append_string(&want, &want_size, &want_length, line, strlen(line));
		}
	}

	if (want_length == 0)
		return (NULL);

	if (want_length > 3276800)
		errc(EXIT_FAILURE, E2BIG, "build_repair_command: There are too many files to repair -- please re-clone the repository");

	if ((command = (char *)malloc(BUFFER_UNIT_SMALL + want_length)) == NULL)
		err(EXIT_FAILURE, "build_repair_command: malloc");

	snprintf(command,
		BUFFER_UNIT_SMALL + want_length,
		"0011command=fetch"
		"%04x%s0001"
		"000dthin-pack"
		"000fno-progress"
		"000dofs-delta"
		"%s"
		"000cdeepen 1"
		"0009done\n0000",
		agent_length,
		connection->agent,
		want);

	return (command);
}


/*
 * get_commit_details
 */

static void
get_commit_details(connector *connection)
{
	char       command[BUFFER_UNIT_SMALL], ref[BUFFER_UNIT_SMALL], peeled[BUFFER_UNIT_SMALL], want[41];
	char      *position = NULL, *end = NULL;
	time_t     current;
	struct tm  now;
	int        tries = 2, year = 0, quarter = 0, pack_file_name_size = 0;
	uint8_t    agent_length = 0;
	bool       detached = (connection->want != NULL ? true : false);

	/* Send the initial info/refs command. */

	snprintf(command,
		BUFFER_UNIT_SMALL,
		"GET %s/info/refs?service=git-upload-pack HTTP/1.1\r\n"
		"Host: %s:%d\r\n"
		"User-Agent: gitup/%s\r\n"
		"Git-Protocol: version=2\r\n"
		"\r\n",
		connection->repository,
		connection->host,
		connection->port,
		GITUP_VERSION);

	process_command(connection, command);

	if (connection->verbosity > 1)
		printf("%s\n", connection->response);

	/* Make sure the server supports the version 2 protocol. */

	if (strnstr(connection->response, "version 2", strlen(connection->response)) == NULL)
		errc(EXIT_FAILURE, EPROTONOSUPPORT, "%s does not support the version 2 wire protocol", connection->host);

	/* Extract the agent. */

	position = strstr(connection->response, "agent=");
	end      = strstr(position, "\n");

	*end = '\0';
	connection->agent = strdup(position);
	*end = '\n';

	agent_length = strlen(connection->agent) + 4;

	/* Fetch the list of refs. */

	snprintf(command,
		BUFFER_UNIT_SMALL,
		"0014command=ls-refs\n"
		"%04x%s"
		"0016object-format=sha1"
		"0001"
		"0009peel\n"
		"000csymrefs\n"
		"0014ref-prefix HEAD\n"
		"001bref-prefix refs/heads/\n"
		"001aref-prefix refs/tags/\n"
		"0000",
		agent_length,
		connection->agent);

	send_command(connection, command);

	if (connection->verbosity > 1)
		printf("%s\n", connection->response);

	/* Extract the "want" checksum. */

	want[0] = '\0';

	while ((tries-- > 0) && (want[0] == '\0') && (detached == false)) {
		if (strncmp(connection->branch, "quarterly", 9) == 0) {
			/* If the current calendar quarter doesn't exist, try the previous one. */

			current = time(NULL);
			now     = *localtime(&current);
			year    = 1900 + now.tm_year + ((tries == 0) && (now.tm_mon < 3) ? -1 : 0);
			quarter = ((now.tm_mon / 3) + (tries == 0 ? 3 : 0)) % 4 + 1;

			snprintf(ref, BUFFER_UNIT_SMALL, " refs/heads/branches/%04dQ%d", year, quarter);

			/* Retain the name of the quarterly branch being used. */

			free(connection->branch);
			connection->branch = strdup(ref + 12);
		} else if (connection->tag != NULL) {
			snprintf(ref, BUFFER_UNIT_SMALL, " refs/tags/%s", connection->tag);
		} else {
			snprintf(ref, BUFFER_UNIT_SMALL, " refs/heads/%s", connection->branch);
		}

		/* Look for the "want" in peeled references first, then look before the ref. */

		snprintf(peeled, sizeof(peeled), "%s peeled:", ref);

		if ((position = strstr(connection->response, peeled)) != NULL)
			memcpy(want, position + strlen(peeled), 40);
		else if ((position = strstr(connection->response, ref)) != NULL)
			memcpy(want, position - 40, 40);
		else if (tries == 0)
			errc(EXIT_FAILURE, EINVAL, "get_commit_details:%s doesn't exist in %s", ref, connection->repository);
	}

	if (want[0] != '\0') {
		if (connection->want == NULL)
			if ((connection->want = (char *)malloc(41)) == NULL)
				err(EXIT_FAILURE, "get_commit_details: malloc");

		memcpy(connection->want, want, 40);
		connection->want[40] = '\0';

		if (connection->verbosity)
			fprintf(stderr, "# Want: %s\n", connection->want);
	}

	/* Because there is no way to lookup commit history, if a want commit is
	   specified, change the branch to (detached). */

	if (detached == true) {
		free(connection->branch);
		connection->branch = strdup("(detached)");
	}

	if ((connection->verbosity) && (connection->tag == NULL))
		fprintf(stderr, "# Branch: %s\n", connection->branch);

	/* Create the pack file name. */

	if (connection->keep_pack_file == true) {
		pack_file_name_size = strlen(connection->section) + 47;

		if ((connection->pack_file = (char *)malloc(pack_file_name_size + 1)) == NULL)
			err(EXIT_FAILURE, "get_commit_details: malloc");

		snprintf(connection->pack_file, pack_file_name_size, "%s-%s.pack", connection->section, connection->want);

		if (connection->verbosity)
			fprintf(stderr, "# Saving pack file: %s\n", connection->pack_file);
	}
}


/*
 * load_pack
 *
 * Procedure that loads a local copy of the pack data or fetches it from the server.
 */

static void
load_pack(connector *connection)
{
	char hash_buffer[20];
	int  pack_size = 0;

	load_file(connection->pack_file, &connection->response, &(connection->response_size));
	pack_size = connection->response_size - 20;

	/* Verify the pack data checksum. */

	SHA1((unsigned char *)connection->response, pack_size, (unsigned char *)hash_buffer);

	if (memcmp(connection->response + pack_size, hash_buffer, 20) != 0)
		errc(EXIT_FAILURE, EAUTH, "fetch_pack: pack checksum mismatch -- expected: %s, received: %s", legible_hash(connection->response + pack_size), legible_hash(hash_buffer));

	/* Process the pack data. */

	unpack_objects(connection);
}


/*
 * fetch_pack
 *
 * Procedure that fetches pack data from the server.
 */

static void
fetch_pack(connector *connection, char *command)
{
	char *pack_start = NULL, hash_buffer[20];
	int   chunk_size = 1, pack_size = 0, source = 0, target = 0;

	/* Request the pack data. */

	send_command(connection, command);

	/* Find the start of the pack data and remove the header. */

	if ((pack_start = strstr(connection->response, "PACK")) == NULL)
		errc(EXIT_FAILURE, EFTYPE, "fetch_pack: malformed pack data:\n%s", connection->response);

	pack_start -= 5;
	connection->response_size -= (pack_start - connection->response + 11);
	memmove(connection->response, connection->response + 8, 4);

	/* Remove the chunk size markers from the pack data. */

	source = pack_start - connection->response;

	while (chunk_size > 0) {
		chunk_size = strtol(connection->response + source, (char **)NULL, 16);

		if (chunk_size == 0)
			break;

		memmove(connection->response + target, connection->response + source + 5, chunk_size - 5);
		target += chunk_size - 5;
		source += chunk_size;
		connection->response_size -= 5;
	}

	connection->response_size += 5;
	pack_size = connection->response_size - 20;

	/* Verify the pack data checksum. */

	SHA1((unsigned char *)connection->response, pack_size, (unsigned char *)hash_buffer);

	if (memcmp(connection->response + pack_size, hash_buffer, 20) != 0)
		errc(EXIT_FAILURE, EAUTH, "fetch_pack: pack checksum mismatch -- expected: %s, received: %s", legible_hash(connection->response + pack_size), legible_hash(hash_buffer));

	/* Save the pack data. */

	if (connection->keep_pack_file == true)
		save_file(connection->pack_file, 0644, connection->response, connection->response_size, 0, 0);

	/* Process the pack data. */

	unpack_objects(connection);

	free(command);
}


/*
 * store_object
 *
 * Procedure that creates a new object and stores it in the array and lookup tree.
 */

static void
store_object(connector *connection, int type, char *buffer, int buffer_size, int pack_offset, int index_delta, char *ref_delta_hash)
{
	struct object_node *object = NULL, find;
	char               *hash = NULL;

	hash = calculate_object_hash(buffer, buffer_size, type);

	/* Check to make sure the object doesn't already exist. */

	find.hash = hash;

	if (((object = RB_FIND(Tree_Objects, &Objects, &find)) != NULL) && (connection->repair == false)) {
		free(hash);
	} else {
		/* Extend the array if needed, create a new node and add it. */

		if (connection->objects % BUFFER_UNIT_SMALL == 0)
			if ((connection->object = (struct object_node **)realloc(connection->object, (connection->objects + BUFFER_UNIT_SMALL) * sizeof(struct object_node *))) == NULL)
				err(EXIT_FAILURE, "store_object: realloc");

		if ((object = (struct object_node *)malloc(sizeof(struct object_node))) == NULL)
			err(EXIT_FAILURE, "store_object: malloc");

		object->index          = connection->objects;
		object->type           = type;
		object->hash           = hash;
		object->pack_offset    = pack_offset;
		object->index_delta    = index_delta;
		object->ref_delta_hash = (ref_delta_hash ? legible_hash(ref_delta_hash) : NULL);
		object->buffer         = buffer;
		object->buffer_size    = buffer_size;

		if (connection->verbosity > 1)
			fprintf(stdout, "###### %05d-%d\t%d\t%u\t%s\t%d\t%s\n", object->index, object->type, object->pack_offset, object->buffer_size, object->hash, object->index_delta, object->ref_delta_hash);

		if (type < 6)
			RB_INSERT(Tree_Objects, &Objects, object);

		connection->object[connection->objects++] = object;
	}
}


/*
 * unpack_objects
 *
 * Procedure that extracts all of the objects from the pack data.
 */

static void
unpack_objects(connector *connection)
{
	int            buffer_size = 0, total_objects = 0, object_type = 0, index_delta = 0;
	int            stream_code = 0, version = 0, stream_bytes = 0, x = 0;
	char          *buffer = NULL, *ref_delta_hash = NULL;
	uint32_t       file_size = 0, file_bits = 0, pack_offset = 0, lookup_offset = 0, position = 4;
	unsigned char  zlib_out[16384];

	/* Check the pack version number. */

	version   = (unsigned char)connection->response[position + 3];
	position += 4;

	if (version != 2)
		errc(EXIT_FAILURE, EFTYPE, "unpack_objects: pack version %d not supported", version);

	/* Determine the number of objects in the pack data. */

	for (x = 0; x < 4; x++, position++)
		total_objects = (total_objects << 8) + (unsigned char)connection->response[position];

	if (connection->verbosity > 1)
		fprintf(stderr, "\npack version: %d, total_objects: %d, pack_size: %d\n\n", version, total_objects, connection->response_size);

	/* Unpack the objects. */

	while ((position < connection->response_size) && (total_objects-- > 0)) {
		object_type    = (unsigned char)connection->response[position] >> 4 & 0x07;
		pack_offset    = position;
		index_delta    = 0;
		file_size      = 0;
		stream_bytes   = 0;
		ref_delta_hash = NULL;

		/* Extract the file size. */

		do {
			file_bits  = connection->response[position] & (stream_bytes == 0 ? 0x0F : 0x7F);
			file_size += (stream_bytes == 0 ? file_bits : file_bits << (4 + 7 * (stream_bytes - 1)));
			stream_bytes++;
		}
		while (connection->response[position++] & 0x80);

		/* Find the object->index referred to by the ofs-delta. */

		if (object_type == 6) {
			lookup_offset = 0;
			index_delta   = connection->objects;

			do lookup_offset = (lookup_offset << 7) + (connection->response[position] & 0x7F) + 1;
			while (connection->response[position++] & 0x80);

			while (--index_delta > 0)
				if (pack_offset - lookup_offset + 1 == connection->object[index_delta]->pack_offset)
					break;

			if (index_delta == 0)
				errc(EXIT_FAILURE, EINVAL, "unpack_objects: cannot find ofs-delta base object");
		}

		/* Extract the ref-delta checksum. */

		if (object_type == 7) {
			if ((ref_delta_hash = (char *)malloc(20)) == NULL)
				err(EXIT_FAILURE, "unpack_objects: malloc");

			memcpy(ref_delta_hash, connection->response + position, 20);
			position += 20;
		}

		/* Inflate and store the object. */

		buffer      = NULL;
		buffer_size = 0;

		z_stream stream = {
			.zalloc   = Z_NULL,
			.zfree    = Z_NULL,
			.opaque   = Z_NULL,
			.avail_in = connection->response_size - position,
			.next_in  = (unsigned char *)(connection->response + position),
			};

		stream_code = inflateInit(&stream);

		if (stream_code == Z_DATA_ERROR)
			errc(EXIT_FAILURE, EILSEQ, "unpack_objects: zlib data stream failure");

		do {
			stream.avail_out = 16384,
			stream.next_out  = zlib_out;
			stream_code      = inflate(&stream, Z_NO_FLUSH);
			stream_bytes     = 16384 - stream.avail_out;

			if ((buffer = (char *)realloc(buffer, buffer_size + stream_bytes)) == NULL)
				err(EXIT_FAILURE, "unpack_objects: realloc");

			memcpy(buffer + buffer_size, zlib_out, stream_bytes);
			buffer_size += stream_bytes;
		}
		while (stream.avail_out == 0);

		inflateEnd(&stream);
		position += stream.total_in;

		store_object(connection, object_type, buffer, buffer_size, pack_offset, index_delta, ref_delta_hash);

		free(ref_delta_hash);
	}
}


/*
 * unpack_delta_integer
 *
 * Function that reconstructs a 32 bit integer from the data stream.
 */

static uint32_t
unpack_delta_integer(char *data, uint32_t *position, int bits)
{
	uint32_t result = 0, read_bytes = 0, temp = 0, mask = 8;

	/* Determine how many bytes in the stream are needed. */

	do if (bits & mask) read_bytes++;
	while (mask >>= 1);

	/* Put the bytes in their proper position based on the bit field passed in. */

	if (read_bytes > 0) {
		temp = read_bytes;
		mask = 3;

		do {
			if (bits & (1 << mask))
				result += ((unsigned char)data[*position + --temp] << (mask * 8));
		}
		while (mask-- > 0);

		*position += read_bytes;
	}

	return (result);
}


/*
 * unpack_variable_length_integer
 *
 * Function that reconstructs a variable length integer from the data stream.
 */

static uint32_t
unpack_variable_length_integer(char *data, uint32_t *position)
{
	uint32_t result = 0, count = 0;

	do result += (data[*position] & 0x7F) << (7 * count++);
	while (data[(*position)++] & 0x80);

	return (result);
}


/*
 * apply_deltas
 *
 * Procedure that applies the changes in all of the delta objects to their
 * base objects.
 */

static void
apply_deltas(connector *connection)
{
	struct object_node *delta, *base, lookup;
	int                 instruction = 0, length_bits = 0, x = 0, o = 0, offset_bits = 0;
	int                 delta_count = -1, deltas[BUFFER_UNIT_SMALL];
	char               *start, *merge_buffer = NULL, *layer_buffer = NULL;
	uint32_t            offset = 0, position = 0, length = 0, layer_buffer_size = 0, merge_buffer_size = 0;
	uint32_t            old_file_size = 0, new_file_size = 0, new_position = 0;

	for (o = connection->objects - 1; o >= 0; o--) {
		merge_buffer = NULL;
		delta        = connection->object[o];
		delta_count  = 0;

		if (delta->type < 6)
			continue;

		/* Follow the chain of ofs-deltas down to the base object. */

		while (delta->type == 6) {
			deltas[delta_count++] = delta->index;
			delta = connection->object[delta->index_delta];
			lookup.hash = delta->hash;
		}

		/* Find the ref-delta base object. */

		if (delta->type == 7) {
			deltas[delta_count++] = delta->index;
			lookup.hash = delta->ref_delta_hash;
			load_object(connection, lookup.hash, NULL);
		}

		/* Lookup the base object and setup the merge buffer. */

		if ((base = RB_FIND(Tree_Objects, &Objects, &lookup)) == NULL)
			errc(EXIT_FAILURE, ENOENT, "apply_deltas: cannot find %05d -> %d/%s", delta->index, delta->index_delta, delta->ref_delta_hash);

		if ((merge_buffer = (char *)malloc(base->buffer_size)) == NULL)
			err(EXIT_FAILURE, "apply_deltas: malloc");

		memcpy(merge_buffer, base->buffer, base->buffer_size);
		merge_buffer_size = base->buffer_size;

		/* Loop though the deltas to be applied. */

		for (x = delta_count - 1; x >= 0; x--) {
			delta         = connection->object[deltas[x]];
			position      = 0;
			new_position  = 0;
			old_file_size = unpack_variable_length_integer(delta->buffer, &position);
			new_file_size = unpack_variable_length_integer(delta->buffer, &position);

			/* Make sure the layer buffer is large enough. */

			if (new_file_size > layer_buffer_size) {
				layer_buffer_size = new_file_size;

				if ((layer_buffer = (char *)realloc(layer_buffer, layer_buffer_size)) == NULL)
					err(EXIT_FAILURE, "apply_deltas: realloc");
			}

			/* Loop through the copy/insert instructions and build up the layer buffer. */

			while (position < delta->buffer_size) {
				instruction = (unsigned char)delta->buffer[position++];

				if (instruction & 0x80) {
					length_bits = (instruction & 0x70) >> 4;
					offset_bits = (instruction & 0x0F);

					offset = unpack_delta_integer(delta->buffer, &position, offset_bits);
					start  = merge_buffer + offset;
					length = unpack_delta_integer(delta->buffer, &position, length_bits);

					if (length == 0)
						length = 65536;
				} else {
					offset    = position;
					start     = delta->buffer + offset;
					length    = instruction;
					position += length;
				}

				if (new_position + length > new_file_size)
					errc(EXIT_FAILURE, ERANGE, "apply_deltas: position overflow -- %u + %u > %u", new_position, length, new_file_size);

				memcpy(layer_buffer + new_position, start, length);
				new_position += length;
			}

			/* Make sure the merge buffer is large enough. */

			if (new_file_size > merge_buffer_size) {
				merge_buffer_size = new_file_size;

				if ((merge_buffer = (char *)realloc(merge_buffer, merge_buffer_size)) == NULL)
					err(EXIT_FAILURE, "apply_deltas: realloc");
			}

			/* Store the layer buffer in the merge buffer for the next loop iteration. */

			memcpy(merge_buffer, layer_buffer, new_file_size);
		}

		/* Store the completed object. */

		store_object(connection, base->type, merge_buffer, new_file_size, 0, 0, NULL);
	}
}


/*
 * extract_tree_item
 *
 * Procedure that extracts mode/path/hash items in a tree and returns them in a new file_node.
 */

static void
extract_tree_item(struct file_node *file, char **position)
{
	int x = 0, path_size = 0;

	/* Extract the file mode. */

	file->mode = strtol(*position, (char **)NULL, 8);
	*position  = strchr(*position, ' ') + 1;

	/* Extract the file path. */

	path_size = strlen(*position) + 1;
	snprintf(file->path, path_size, "%s", *position);
	*position += path_size;

	/* Extract the file SHA checksum. */

	for (x = 0; x < 20; x++)
		snprintf(&file->hash[x * 2], 3, "%02x", (unsigned char)*(*position)++);

	file->hash[40] = '\0';
}


/*
 * save_tree
 *
 * Procedure that processes all of the obj-trees and retains the current files.
 */

static void
process_tree(connector *connection, int remote_descriptor, char *hash, char *base_path)
{
	struct object_node object, *found_object = NULL, *tree = NULL;
	struct file_node   file, *found_file = NULL, *new_file_node = NULL, *remote_file = NULL;
	char               full_path[BUFFER_UNIT_SMALL], line[BUFFER_UNIT_SMALL], *position = NULL, *buffer = NULL;
	unsigned int       buffer_size = 0, buffer_length = 0;

	if ((mkdir(base_path, 0755) == -1) && (errno != EEXIST))
		err(EXIT_FAILURE, "process_tree: cannot create %s", base_path);

	object.hash = hash;

	if ((tree = RB_FIND(Tree_Objects, &Objects, &object)) == NULL)
		errc(EXIT_FAILURE, ENOENT, "process_tree: tree %s -- %s cannot be found", base_path, object.hash);

	/* Remove the base path from the list of upcoming deletions. */

	file.path = base_path;

	if ((found_file = RB_FIND(Tree_Local_Path, &Local_Path, &file)) != NULL) {
		found_file->keep = true;
		found_file->save = false;
		found_file->new  = false;
	}

	/* Add the base path to the output. */

	if ((file.path = (char *)malloc(BUFFER_UNIT_SMALL)) == NULL)
		err(EXIT_FAILURE, "process_tree: malloc");

	if ((file.hash = (char *)malloc(41)) == NULL)
		err(EXIT_FAILURE, "process_tree: malloc");

	snprintf(line, sizeof(line), "%o\t%s\t%s/\n", 040000, hash, base_path);
	append_string(&buffer, &buffer_size, &buffer_length, line, strlen(line));

	/* Process the tree items. */

	position = tree->buffer;

	while ((uint32_t)(position - tree->buffer) < tree->buffer_size) {
		extract_tree_item(&file, &position);

		snprintf(full_path, sizeof(full_path), "%s/%s", base_path, file.path);

		snprintf(line, sizeof(line), "%o\t%s\t%s\n", file.mode, file.hash, file.path);
		append_string(&buffer, &buffer_size, &buffer_length, line, strlen(line));

		/* Recursively walk the trees and process the files/links. */

		if (S_ISDIR(file.mode)) {
			process_tree(connection, remote_descriptor, file.hash, full_path);
		} else {
			/* Locate the pack file object and local copy of the file. */

			memcpy(object.hash, file.hash, 41);
			memcpy(file.path, full_path, strlen(full_path) + 1);

			found_object = RB_FIND(Tree_Objects, &Objects, &object);
			found_file   = RB_FIND(Tree_Local_Path, &Local_Path, &file);

			/* If the local file hasn't changed, skip it. */

			if (found_file != NULL) {
				found_file->keep = true;
				found_file->save = false;
				found_file->new  = false;

				if (strncmp(file.hash, found_file->hash, 40) == 0)
					continue;
			}

			/* Missing objects can sometimes be found by searching the local tree. */

			if (found_object == NULL) {
				load_object(connection, file.hash, full_path);
				found_object = RB_FIND(Tree_Objects, &Objects, &object);
			}

			/* If the object is still missing, exit. */

			if (found_object == NULL)
				errc(EXIT_FAILURE, ENOENT, "process_tree: file %s -- %s cannot be found", full_path, file.hash);

			/* Otherwise retain it. */

			if ((remote_file = RB_FIND(Tree_Remote_Path, &Remote_Path, &file)) == NULL) {
				if ((new_file_node = (struct file_node *)malloc(sizeof(struct file_node))) == NULL)
					err(EXIT_FAILURE, "process_tree: malloc");

				new_file_node->mode = file.mode;
				new_file_node->hash = strdup(found_object->hash);
				new_file_node->path = strdup(full_path);
				new_file_node->keep = true;
				new_file_node->save = true;
				new_file_node->new  = (found_file == NULL);

				RB_INSERT(Tree_Remote_Path, &Remote_Path, new_file_node);
			} else {
				free(remote_file->hash);
				remote_file->mode = file.mode;
				remote_file->hash = strdup(found_object->hash);
				remote_file->keep = true;
				remote_file->save = true;
				remote_file->new  = (found_file == NULL);
			}
		}
	}

	/* Add the tree data to the remote files list. */

	write(remote_descriptor, buffer, buffer_length);
	write(remote_descriptor, "\n", 1);

	free(buffer);
	free(file.hash);
	free(file.path);
}


/*
 * save_repairs
 *
 * Procedure that saves the repaired files.
 */

static void
save_repairs(connector *connection)
{
	struct object_node  find_object, *found_object = NULL;
	struct file_node   *local_file = NULL, *remote_file = NULL, *found_file = NULL;
	struct stat         check_file;
	char               *check_hash = NULL, *buffer_hash = NULL;
	bool                missing = false, update = false;

	/* Loop through the remote file list, looking for objects that arrived in the pack data. */

	RB_FOREACH(found_file, Tree_Remote_Path, &Remote_Path) {
		find_object.hash = found_file->hash;

		if ((found_object = RB_FIND(Tree_Objects, &Objects, &find_object)) == NULL)
			continue;

		/* Save the object. */

		if (S_ISDIR(found_file->mode)) {
			if ((mkdir(found_file->path, 0755) == -1) && (errno != EEXIST))
				err(EXIT_FAILURE, "save_repairs: cannot create %s", found_file->path);
		} else {
			missing = stat(found_file->path, &check_file);
			update  = true;

			/* Because identical files can exist in multiple places, only update the altered files. */

			if (missing == false) {
				check_hash  = calculate_file_hash(found_file->path, found_file->mode);
				buffer_hash = calculate_object_hash(found_object->buffer, found_object->buffer_size, 3);

				if (strncmp(check_hash, buffer_hash, 40) == 0)
					update = false;
			}

			if (update == true)
				save_file(found_file->path, found_file->mode, found_object->buffer, found_object->buffer_size, connection->verbosity, missing);
		}
	}

	/* Make sure no files are deleted. */

	RB_FOREACH(remote_file, Tree_Remote_Path, &Remote_Path)
		if ((local_file = RB_FIND(Tree_Local_Path, &Local_Path, remote_file)) != NULL)
			local_file->keep = true;
}


/*
 * save_objects
 *
 * Procedure that commits the objects and trees to disk.
 */

static void
save_objects(connector *connection)
{
	struct object_node *found_object = NULL, find_object;
	struct file_node   *found_file = NULL;
	char                tree[41], remote_files_new[BUFFER_UNIT_SMALL];
	int                 fd;

	/* Find the tree object referenced in the commit. */

	find_object.hash = connection->want;

	if ((found_object = RB_FIND(Tree_Objects, &Objects, &find_object)) == NULL)
		errc(EXIT_FAILURE, EINVAL, "save_objects: cannot find %s", connection->want);

	if (memcmp(found_object->buffer, "tree ", 5) != 0)
		errc(EXIT_FAILURE, EINVAL, "save_objects: first object is not a commit");

	memcpy(tree, found_object->buffer + 5, 40);
	tree[40] = '\0';

	/* Recursively start processing the tree. */

	snprintf(remote_files_new, BUFFER_UNIT_SMALL, "%s.new", connection->remote_files);

	if (((fd = open(remote_files_new, O_WRONLY | O_CREAT | O_TRUNC)) == -1) && (errno != EEXIST))
		err(EXIT_FAILURE, "save_objects: write file failure %s", remote_files_new);

	chmod(remote_files_new, 0644);
	write(fd, connection->want, strlen(connection->want));
	write(fd, "\n", 1);
	process_tree(connection, fd, tree, connection->path_target);
	close(fd);

	/* Save the remote files list. */

	if (((remove(connection->remote_files)) != 0) && (errno != ENOENT))
		err(EXIT_FAILURE, "save_objects: cannot remove %s", connection->remote_files);

	if ((rename(remote_files_new, connection->remote_files)) != 0)
		err(EXIT_FAILURE, "save_objects: cannot rename %s", connection->remote_files);

	/* Save all of the new and modified files. */

	RB_FOREACH(found_file, Tree_Remote_Path, &Remote_Path)
		if (found_file->save) {
			find_object.hash = found_file->hash;

			if ((found_object = RB_FIND(Tree_Objects, &Objects, &find_object)) == NULL)
				errc(EXIT_FAILURE, EINVAL, "save_objects: cannot find %s", found_file->hash);

			save_file(found_file->path, found_file->mode, found_object->buffer, found_object->buffer_size, connection->verbosity, found_file->new);
		}
}


/*
 * load_configuration
 *
 * Procedure that loads the section options from gitup.conf
 */

static int
load_configuration(connector *connection, const char *configuration_file, char **argv, int argc)
{
	struct ucl_parser  *parser = NULL;
	ucl_object_t       *object = NULL;
	const ucl_object_t *section = NULL, *pair = NULL, *ignore = NULL;
	ucl_object_iter_t   it = NULL, it_section = NULL, it_ignores = NULL;
	const char         *key = NULL, *config_section = NULL;
	char               *sections = NULL, temp_path[BUFFER_UNIT_SMALL];
	unsigned int        sections_size = 1024, sections_length = 0;
	uint8_t             argument_index = 0, x = 0;
	struct stat         check_file;

	if ((sections = (char *)malloc(sections_size)) == NULL)
		err(EXIT_FAILURE, "load_configuration: malloc");

	/* If the configuration file is not actually a file, libucl doesn't set its
	   error message to something helpful, so check it first. */

	stat(configuration_file, &check_file);

	if (!S_ISREG(check_file.st_mode))
		errc(EXIT_FAILURE, EFTYPE, "load_configuration: cannot load %s", configuration_file);

	/* Load and process the configuration file. */

	parser = ucl_parser_new(0);

	if (ucl_parser_add_file(parser, configuration_file) == false) {
		fprintf(stderr, "load_configuration: %s\n", ucl_parser_get_error(parser));
		exit(EXIT_FAILURE);
	}

	object = ucl_parser_get_object(parser);

	while ((connection->section == NULL) && (section = ucl_iterate_object(object, &it, true))) {
		config_section = ucl_object_key(section);

		/* Look for the section in the command line arguments. */

		for (x = 0; x < argc; x++) {
			if ((strlen(argv[x]) == 2) && (strncmp(argv[x], "-V", 2)) == 0) {
				fprintf(stdout, "gitup version %s\n", GITUP_VERSION);
				exit(EXIT_SUCCESS);
			}

			if ((strlen(argv[x]) == strlen(config_section)) && (strncmp(argv[x], config_section, strlen(config_section)) == 0)) {
				connection->section = strdup(argv[x]);
				argument_index = x;
			}
		}

		/* Add the section to the list of known sections in case a valid section is not found. */

		if (strncmp(config_section, "defaults", 8) != 0) {
			append_string(&sections, &sections_size, &sections_length, "\t * ", 4);
			append_string(&sections, &sections_size, &sections_length, config_section, strlen(config_section));
			append_string(&sections, &sections_size, &sections_length, "\n", 1);

			if (argument_index == 0)
				continue;
		}

		/* Iterate through the section's configuration parameters. */

		while ((pair = ucl_iterate_object(section, &it_section, true))) {
			key = ucl_object_key(pair);

			if (strstr(key, "branch") != NULL)
				connection->branch = strdup(ucl_object_tostring(pair));

			if (strstr(key, "host") != NULL)
				connection->host = strdup(ucl_object_tostring(pair));

			if (((strstr(key, "ignore") != NULL) || (strstr(key, "ignores") != NULL)) && (ucl_object_type(pair) == UCL_ARRAY))
				while ((ignore = ucl_iterate_object(pair, &it_ignores, true))) {
					if ((connection->ignore = (char **)realloc(connection->ignore, (connection->ignores + 1) * sizeof(char *))) == NULL)
						err(EXIT_FAILURE, "set_configuration_parameters: malloc");

					snprintf(temp_path, sizeof(temp_path), "%s", ucl_object_tostring(ignore));

					if (temp_path[0] != '/')
						snprintf(temp_path, sizeof(temp_path), "%s/%s", connection->path_target, ucl_object_tostring(ignore));

					connection->ignore[connection->ignores++] = strdup(temp_path);
				}

			if (strstr(key, "port") != NULL) {
				if (ucl_object_type(pair) == UCL_INT)
					connection->port = ucl_object_toint(pair);
				else
					connection->port = strtol(ucl_object_tostring(pair), (char **)NULL, 10);
			}

			if ((strstr(key, "repository_path") != NULL) || (strstr(key, "repository") != NULL))
				connection->repository = strdup(ucl_object_tostring(pair));

			if ((strstr(key, "target_directory") != NULL) || (strstr(key, "target") != NULL))
				connection->path_target = strdup(ucl_object_tostring(pair));

			if (strstr(key, "verbosity") != NULL) {
				if (ucl_object_type(pair) == UCL_INT)
					connection->verbosity = ucl_object_toint(pair);
				else
					connection->verbosity = strtol(ucl_object_tostring(pair), (char **)NULL, 10);
			}

			if (strstr(key, "work_directory") != NULL)
				connection->path_work = strdup(ucl_object_tostring(pair));
		}
	}

	ucl_object_unref(object);
	ucl_parser_free(parser);

	/* Check to make sure all of the required information was found in the config file. */

	if (argument_index == 0)
		errc(EXIT_FAILURE, EINVAL, "\nCannot find a matching section in the command line arguments.  These are the configured sections:\n%s", sections);

	if (connection->branch == NULL)
		errc(EXIT_FAILURE, EINVAL, "No branch found in [%s]", connection->section);

	if (connection->host == NULL)
		errc(EXIT_FAILURE, EDESTADDRREQ, "No host found in [%s]", connection->section);

	if (connection->path_target == NULL)
		errc(EXIT_FAILURE, EINVAL, "No target path found in [%s]", connection->section);

	if (connection->path_work == NULL)
		errc(EXIT_FAILURE, EINVAL, "No work directory found in [%s]", connection->section);

	if (connection->port == 0)
		errc(EXIT_FAILURE, EDESTADDRREQ, "No port found in [%s]", connection->section);

	if (connection->repository == NULL)
		errc(EXIT_FAILURE, EINVAL, "No repository found in [%s]", connection->section);

	free(sections);

	return (argument_index);
}


/*
 * usage
 *
 * Procedure that prints a summary of command line options and exits.
 */

static void
usage(const char *configuration_file)
{
	fprintf(stderr, "Usage: gitup <section> [-ckrV] [-h checksum] [-t tag] [-u pack file] [-v verbosity] [-w checksum]\n");
	fprintf(stderr, "  Please see %s for the list of <section> options.\n\n", configuration_file);
	fprintf(stderr, "  Options:\n");
	fprintf(stderr, "    -C  Override the default configuration file.\n");
	fprintf(stderr, "    -c  Force gitup to clone the repository.\n");
	fprintf(stderr, "    -h  Override the 'have' checksum.\n");
	fprintf(stderr, "    -k  Save a copy of the pack data to the current working directory.\n");
	fprintf(stderr, "    -r  Repair all missing/modified files in the local repository.\n");
	fprintf(stderr, "    -t  Fetch the commit referenced by the specified tag.\n");
	fprintf(stderr, "    -u  Path to load a copy of the pack data, skipping the download.\n");
	fprintf(stderr, "    -v  How verbose the output should be (0 = no output, 1 = the default\n");
	fprintf(stderr, "          normal output, 2 = also show debugging information).\n");
	fprintf(stderr, "    -V  Display gitup's version number and exit.\n");
	fprintf(stderr, "    -w  Override the 'want' checksum.\n");
	fprintf(stderr, "\n");

	exit(EXIT_FAILURE);
}


/*
 * main
 *
 * A lightweight, dependency-free program to clone/pull a Git repository.
 */

int
main(int argc, char **argv)
{
	struct object_node *object = NULL, *next_object = NULL;
	struct file_node   *file   = NULL, *next_file = NULL;
	struct stat         check_file;
	const char         *configuration_file = CONFIG_FILE_PATH;
	char               *command = NULL, *start = NULL, *temp = NULL, *extension = NULL, *want = NULL, section[BUFFER_UNIT_SMALL];
	char                gitup_revision[BUFFER_UNIT_SMALL], gitup_revision_path[BUFFER_UNIT_SMALL];
	int                 x = 0, o = 0, option = 0, length = 0, skip_optind = 0;
	bool                ignore = false, current_repository = false, encoded = false;
	bool                path_target_exists = false, remote_files_exists = false, pack_file_exists = false;

	connector connection = {
		.ssl               = NULL,
		.ctx               = NULL,
		.socket_descriptor = 0,
		.host              = NULL,
		.port              = 0,
		.agent             = NULL,
		.section           = NULL,
		.repository        = NULL,
		.branch            = NULL,
		.tag               = NULL,
		.have              = NULL,
		.want              = NULL,
		.response          = NULL,
		.response_blocks   = 0,
		.response_size     = 0,
		.clone             = false,
		.repair            = false,
		.object            = NULL,
		.objects           = 0,
		.pack_file         = NULL,
		.path_target       = NULL,
		.path_work         = NULL,
		.remote_files      = NULL,
		.ignore            = NULL,
		.ignores           = 0,
		.keep_pack_file    = false,
		.use_pack_file     = false,
		.verbosity         = 1,
		};

	if (argc < 2)
		usage(configuration_file);

	/* Check first to see if the configuration file path is being overridden. */

	for (x = 0; x < argc; x++)
		if ((strlen(argv[x]) > 1) && (strnstr(argv[x], "-C", 2) == argv[x])) {
			if (strlen(argv[x]) > 2)
				configuration_file = strdup(argv[x] + 2);
			else if ((argc > x) && (argv[x + 1][0] != '-'))
				configuration_file = strdup(argv[x + 1]);
		}

	/* Load the configuration file to learn what section is being requested. */

	skip_optind = load_configuration(&connection, configuration_file, argv, argc);

	if (skip_optind == 1)
		optind++;

	/* Process the command line parameters. */

	while ((option = getopt(argc, argv, "C:ch:krt:u:v:w:")) != -1) {
		switch (option) {
			case 'C':
				if (connection.verbosity)
					fprintf(stderr, "# Configuration file: %s\n", configuration_file);
				break;
			case 'c':
				connection.clone = true;
				break;
			case 'h':
				connection.have = strdup(optarg);
				break;
			case 'k':
				connection.keep_pack_file = true;
				break;
			case 'r':
				connection.repair = true;
				break;
			case 't':
				connection.tag = strdup(optarg);
				break;
			case 'u':
				if (stat(optarg, &check_file) == 0) {
					connection.use_pack_file = true;
					connection.pack_file     = strdup(optarg);

					/* Try and extract the want from the file name. */

					length    = strlen(optarg);
					start     = optarg;
					temp      = optarg;
					extension = strnstr(optarg, ".pack", length);

					while ((temp = strchr(start, '/')) != NULL)
						start = temp + 1;

					want = strnstr(start, connection.section, length - (start - optarg));

					if (want == NULL)
						break;
					else
						want += strlen(connection.section) + 1;

					if (extension != NULL)
						*extension = '\0';

					if (strlen(want) == 40)
						connection.want = strdup(want);
				}
				break;
			case 'v':
				connection.verbosity = strtol(optarg, (char **)NULL, 10);
				break;
			case 'w':
				connection.want = strdup(optarg);
				break;
		}

		if (optind == skip_optind)
			optind++;
	}

	/* If a tag and a want are specified, warn and exit. */

	if ((connection.tag != NULL) && (connection.want != NULL))
		errc(EXIT_FAILURE, EINVAL, "A tag and a want cannot be requested at the same time");

	/* Create the work path and build the remote files path. */

	if ((mkdir(connection.path_work, 0755) == -1) && (errno != EEXIST))
		err(EXIT_FAILURE, "main: cannot create %s", connection.path_work);

	length = strlen(connection.path_work) + strlen(connection.section) + 1;

	if ((connection.remote_files = (char *)malloc(length + 1)) == NULL)
		err(EXIT_FAILURE, "main: malloc");

	snprintf(connection.remote_files, length + 1, "%s/%s", connection.path_work, connection.section);
	temp = strdup(connection.remote_files);

	/* If non-alphanumerics exist in the section, encode them. */

	length = strlen(connection.section);

	for (x = 0; x < length; x++)
		if ((!isalpha(connection.section[x])) && (!isdigit(connection.section[x]))) {
			if ((connection.section = (char *)realloc(connection.section, length + 2)) == NULL)
				err(EXIT_FAILURE, "main: realloc");

			memcpy(section, connection.section + x + 1, length - x);
			snprintf(connection.section + x, length - x + 3, "%%%X%s", connection.section[x], section);

			length += 2;
			x += 2;
			encoded = true;
		}

	if (encoded == true) {
		/* Store the updated remote files path. */

		length += strlen(connection.path_work) + 1;

		if ((connection.remote_files = (char *)realloc(connection.remote_files, length + 1)) == NULL)
			err(EXIT_FAILURE, "main: realloc");

		snprintf(connection.remote_files, length + 1, "%s/%s", connection.path_work, connection.section);

		/* If a non-encoded remote files path exists, try and rename it. */

		if ((stat(temp, &check_file) == 0) && ((rename(temp, connection.remote_files)) != 0))
			err(EXIT_FAILURE, "main: cannot rename %s", connection.remote_files);
	}

	free(temp);

	/* If the remote files list or repository are missing, then a clone must be performed. */

	path_target_exists  = (stat(connection.path_target,  &check_file) == 0 ? true : false);
	remote_files_exists = (stat(connection.remote_files, &check_file) == 0 ? true : false);
	pack_file_exists    = (stat(connection.pack_file,    &check_file) == 0 ? true : false);

	if ((path_target_exists == true) && (remote_files_exists == true))
		load_remote_file_list(&connection);
	else
		connection.clone = true;

	if (path_target_exists == true)
		find_local_tree(&connection, connection.path_target);
	else
		connection.clone = true;

	/* Display connection parameters. */

	if (connection.verbosity) {
		fprintf(stderr, "# Host: %s\n", connection.host);
		fprintf(stderr, "# Port: %d\n", connection.port);
		fprintf(stderr, "# Repository: %s\n", connection.repository);
		fprintf(stderr, "# Target: %s\n", connection.path_target);

		if (connection.use_pack_file == true)
			fprintf(stderr, "# Using pack file: %s\n", connection.pack_file);

		if (connection.tag)
			fprintf(stderr, "# Tag: %s\n", connection.tag);

		if (connection.have)
			fprintf(stderr, "# Have: %s\n", connection.have);

		if (connection.want)
			fprintf(stderr, "# Want: %s\n", connection.want);
	}

	/* Execute the fetch, unpack, apply deltas and save. */

	if ((connection.use_pack_file == true) && (pack_file_exists == true)) {
		if (connection.verbosity)
			fprintf(stderr, "# Action: %s\n", (connection.clone ? "clone" : "pull"));

		load_pack(&connection);
		apply_deltas(&connection);
		save_objects(&connection);
	} else {
		if ((connection.use_pack_file == false) || ((connection.use_pack_file == true) && (pack_file_exists == false)))
			get_commit_details(&connection);

		if ((connection.have != NULL) && (connection.want != NULL) && (strncmp(connection.have, connection.want, 40) == 0))
			current_repository = true;

		/* When pulling, first ensure the local tree is pristine. */

		if ((connection.repair == true) || (connection.clone == false)) {
			command = build_repair_command(&connection);

			if (command != NULL) {
				connection.repair = true;

				if (connection.verbosity)
					fprintf(stderr, "# Action: repair\n");

				fetch_pack(&connection, command);
				apply_deltas(&connection);
				save_repairs(&connection);
			}
		}

		/* Process the clone or pull. */

		if ((current_repository == false) && (connection.repair == false)) {
			if (connection.verbosity)
				fprintf(stderr, "# Action: %s\n", (connection.clone ? "clone" : "pull"));

			if (connection.clone == false)
				command = build_pull_command(&connection);
			else
				command = build_clone_command(&connection);

			fetch_pack(&connection, command);
			apply_deltas(&connection);
			save_objects(&connection);
		}
	}

	/* Save .gituprevision. */

	if ((connection.want != NULL) || (connection.tag != NULL)) {
		snprintf(gitup_revision_path, BUFFER_UNIT_SMALL, "%s/.gituprevision", connection.path_target);

		snprintf(gitup_revision,
			BUFFER_UNIT_SMALL,
			"%s:%.9s\n",
			(connection.tag != NULL ? connection.tag : connection.branch),
			connection.want);

		save_file(gitup_revision_path, 0644, gitup_revision, strlen(gitup_revision), 0, 0);
	}

	/* Wrap it all up. */

	RB_FOREACH_SAFE(file, Tree_Local_Hash, &Local_Hash, next_file)
		RB_REMOVE(Tree_Local_Hash, &Local_Hash, file);

	RB_FOREACH_SAFE(file, Tree_Local_Path, &Local_Path, next_file) {
		if ((file->keep == false) && ((current_repository == false) || (connection.repair == true))) {
			for (x = 0, ignore = false; x < connection.ignores; x++)
				if (strnstr(file->path, connection.ignore[x], strlen(file->path)) != NULL)
					ignore = true;

			if (ignore == false) {
				if (connection.verbosity)
					printf(" - %s\n", file->path);

				if (S_ISDIR(file->mode))
					prune_tree(&connection, file->path);
				else if ((remove(file->path) != 0) && (errno != ENOENT))
					err(EXIT_FAILURE, "main: cannot remove %s", file->path);
			}
		}

		RB_REMOVE(Tree_Local_Path, &Local_Path, file);
		file_node_free(file);
	}

	RB_FOREACH_SAFE(file, Tree_Remote_Path, &Remote_Path, next_file) {
		RB_REMOVE(Tree_Remote_Path, &Remote_Path, file);
		file_node_free(file);
	}

	RB_FOREACH_SAFE(object, Tree_Objects, &Objects, next_object)
		RB_REMOVE(Tree_Objects, &Objects, object);

	for (o = 0; o < connection.objects; o++) {
		if (connection.verbosity > 1)
			fprintf(stdout, "###### %05d-%d\t%d\t%u\t%s\t%d\t%s\n", connection.object[o]->index, connection.object[o]->type, connection.object[o]->pack_offset, connection.object[o]->buffer_size, connection.object[o]->hash, connection.object[o]->index_delta, connection.object[o]->ref_delta_hash);

		object_node_free(connection.object[o]);
	}

	for (x = 0; x < connection.ignores; x++)
		free(connection.ignore[x]);

	free(connection.ignore);
	free(connection.response);
	free(connection.object);
	free(connection.host);
	free(connection.agent);
	free(connection.section);
	free(connection.repository);
	free(connection.branch);
	free(connection.tag);
	free(connection.have);
	free(connection.want);
	free(connection.pack_file);
	free(connection.path_target);
	free(connection.path_work);
	free(connection.remote_files);

	if (connection.ssl) {
		SSL_shutdown(connection.ssl);
		SSL_CTX_free(connection.ctx);
		close(connection.socket_descriptor);
		SSL_free(connection.ssl);
	}

	if (connection.repair == true)
		fprintf(stderr, "# The local repository has been repaired.  Please rerun gitup to pull the latest commit.\n");

	sync();

	return (0);
}
