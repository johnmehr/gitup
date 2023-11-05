/*-
 * Copyright (c) 2012-2023, John Mehr <jmehr@umn.edu>
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

#include <arpa/inet.h>
#include <netinet/in.h>
#include <openssl/evp.h>
#include <openssl/opensslv.h>
#include <openssl/sha.h>
#include <openssl/ssl.h>
#include <openssl/ssl3.h>
#include <openssl/err.h>
#include <private/ucl/ucl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/tree.h>

#include <ctype.h>
#include <dirent.h>
#include <err.h>
#include <errno.h>
#include <fcntl.h>
#include <libutil.h>
#include <netdb.h>
#include <regex.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <zlib.h>

#define GITUP_VERSION     "0.99"
#define BUFFER_4K          4096
#define BUFFER_1M          1048576
#define IGNORE_FORCE_READ  1
#define IGNORE_SKIP_DELETE 2

#ifndef CONFIG_FILE_PATH
#define CONFIG_FILE_PATH "./gitup.conf"
#endif

struct object_node {
	RB_ENTRY(object_node) link;
	char      *hash;
	uint8_t    type;
	uint32_t   index;
	uint32_t   index_delta;
	char      *ref_delta_hash;
	uint32_t   offset_pack;
	off_t      offset_cache;
	char      *buffer;
	uint32_t   buffer_size;
	char     **parent;
	uint8_t    parents;
};

struct file_node {
	RB_ENTRY(file_node) link_hash;
	RB_ENTRY(file_node) link_path;
	mode_t  mode;
	char   *hash;
	char   *path;
	bool    keep;
	bool    save;
};

typedef struct {
	regex_t *pattern;
	bool     negate;
} ignore_node;

typedef struct {
	SSL                 *ssl;
	SSL_CTX             *ctx;
	int                  socket_descriptor;
	char                *source_address;
	char                *host;
	char                *host_bracketed;
	uint16_t             port;
	char                *proxy_host;
	uint16_t             proxy_port;
	char                *proxy_username;
	char                *proxy_password;
	char                *proxy_credentials;
	char                *section;
	char                *repository_path;
	char                *branch;
	char                *tag;
	char                *have;
	char                *want;
	char                *response;
	unsigned long        response_blocks;
	uint32_t             response_size;
	bool                 clone;
	bool                 repair;
	struct object_node **object;
	uint32_t             objects;
	char                *pack_data_file;
	char                *pack_history_file;
	char                *path_target;
	bool                 path_target_custom;
	char                *path_work;
	char                *remote_data_file;
	char                *remote_history_file;
	ignore_node        **ignore;
	uint16_t             ignores;
	bool                 keep_pack_file;
	bool                 use_pack_file;
	bool                 commit_history;
	uint8_t              verbosity;
	uint8_t              display_depth;
	char                *updating;
	bool                 low_memory;
	int                  cache;
	off_t                cache_length;
} connector;

static char *   absolute_path(char *);
static void     add_ignore(connector *, const char *);
static void     append(char **, uint32_t *, const char *, size_t);
static void     apply_deltas(connector *);
static char *   build_clone_command(connector *);
static char *   build_commit_command(connector *);
static char *   build_pull_command(connector *);
static char *   build_repair_command(connector *);
static char *   calculate_file_hash(char *, mode_t);
static char *   calculate_object_hash(char *, uint32_t, int);
static void     connect_server(connector *);
static void     create_tunnel(connector *);
static void     extend_updating_list(connector *, char *);
static void     extract_command_line_want(connector *, char *);
static void     extract_proxy_data(connector *, const char *);
static void     extract_tree_item(struct file_node *, char **);
static void     fetch_pack(connector *, char *);
static int      file_node_compare_hash(const struct file_node *,
                                       const struct file_node *);
static int      file_node_compare_path(const struct file_node *,
                                       const struct file_node *);
static void     file_node_free(struct file_node *);
static void     get_commit_details(connector *);
static bool     ignore_file(connector *, char *, uint8_t);
static char *   illegible_hash(char *);
static char *   legible_hash(char *);
static void     load_buffer(connector *, struct object_node *);
static int      load_config(connector *, const char *, char **, int);
static void     load_config_section(connector *, const ucl_object_t *);
static void     load_file(const char *, char **, uint32_t *);
static void     load_gitignore(connector *);
static void     load_object(connector *, char *, char *);
static void     load_pack(connector *, char *, bool);
static void     load_remote_data(connector *);
static void     make_path(char *, mode_t);
static struct file_node * new_file_node(char *, mode_t, char *, bool, bool);
static int      object_node_compare(const struct object_node *,
                                    const struct object_node *);
static void     object_node_free(struct object_node *);
static bool     path_exists(const char *);
static void     process_command(connector *, char *);
static void     process_tree(connector *, int, char *, char *);
static bool     prune_tree(connector *, char *);
static void     release_buffer(connector *, struct object_node *);
static void     save_commit_history(connector *);
static void     save_file(char *, mode_t, char *, uint64_t, int, int);
static void     save_objects(connector *);
static void     save_repairs(connector *);
static void     scan_local_repository(connector *, char *);
static void     send_command(connector *, char *);
static void     setup_ssl(connector *);
static void     store_object(connector *, uint8_t, char *, uint32_t, uint32_t,
                             uint32_t, char *);
static char *   trim_path(char *, int, bool *);
static uint32_t unpack_delta_integer(char *, uint32_t *, uint8_t);
static uint32_t unpack_integer(char *, uint32_t *);
static void     unpack_objects(connector *);
static void     usage(const char *);


/*
 * node_compare
 *
 * Functions that instruct the red-black trees how to sort keys.
 */

static int
file_node_compare_path(const struct file_node *a, const struct file_node *b)
{
	return (strcmp((a ? a->path : ""), (b ? b->path : "")));
}


static int
file_node_compare_hash(const struct file_node *a, const struct file_node *b)
{
	return (strcmp(
		(a && a->hash ? a->hash : ""),
		(b && b->hash ? b->hash : "")));
}


static int
object_node_compare(const struct object_node *a, const struct object_node *b)
{
	return (strcmp(
		(a && a->hash ? a->hash : ""),
		(b && b->hash ? b->hash : "")));
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
	for (int x = 0; x < node->parents; x++)
		free(node->parent[x]);

	free(node->parent);
	free(node->hash);
	free(node->ref_delta_hash);
	free(node->buffer);
	free(node);
}


static RB_HEAD(Tree_Remote_Path, file_node)
	Remote_Path = RB_INITIALIZER(&Remote_Path);

RB_PROTOTYPE(Tree_Remote_Path, file_node, link_path, file_node_compare_path)
RB_GENERATE(Tree_Remote_Path,  file_node, link_path, file_node_compare_path)

static RB_HEAD(Tree_Local_Path, file_node)
	Local_Path = RB_INITIALIZER(&Local_Path);

RB_PROTOTYPE(Tree_Local_Path, file_node, link_path, file_node_compare_path)
RB_GENERATE(Tree_Local_Path,  file_node, link_path, file_node_compare_path)

static RB_HEAD(Tree_Local_Hash, file_node)
	Local_Hash = RB_INITIALIZER(&Local_Hash);

RB_PROTOTYPE(Tree_Local_Hash, file_node, link_hash, file_node_compare_hash)
RB_GENERATE(Tree_Local_Hash,  file_node, link_hash, file_node_compare_hash)

static RB_HEAD(Tree_Objects, object_node)
	Objects = RB_INITIALIZER(&Objects);

RB_PROTOTYPE(Tree_Objects, object_node, link, object_node_compare)
RB_GENERATE(Tree_Objects,  object_node, link, object_node_compare)

static RB_HEAD(Tree_Trim_Path, file_node)
	Trim_Path = RB_INITIALIZER(&Trim_Path);

RB_PROTOTYPE(Tree_Trim_Path, file_node, link_path, file_node_compare_path)
RB_GENERATE(Tree_Trim_Path,  file_node, link_path, file_node_compare_path)


/*
 * release_buffer
 *
 * Function that frees an object buffer.
 */

static void release_buffer(connector *session, struct object_node *obj)
{
	if (session->low_memory) {
		free(obj->buffer);
		obj->buffer = NULL;
	}
}


/*
 * load_buffer
 *
 * Function that loads an object buffer from disk.
 */

static void load_buffer(connector *session, struct object_node *object)
{
	ssize_t bytes_read = 0;

	if ((session->low_memory) && (!object->buffer)) {
		object->buffer = (char *)malloc(object->buffer_size);

		if (object->buffer == NULL)
			err(EXIT_FAILURE, "load_buffer: malloc");

		lseek(session->cache, object->offset_cache, SEEK_SET);

		bytes_read = read(session->cache,
			object->buffer,
			(size_t)object->buffer_size);

		if (bytes_read != (ssize_t)object->buffer_size)
			err(EXIT_FAILURE,
				"load_buffer: read %ld != %d",
				(long)bytes_read,
				object->buffer_size);
	}
}


/*
 * legible_hash
 *
 * Function that converts a 20 byte binary SHA checksum into a 40 byte
 * human-readable SHA checksum.
 */

static char *
legible_hash(char *hash_buffer)
{
	char *hash = NULL;
	int   x = 0;

	if ((hash = (char *)malloc(41)) == NULL)
		err(EXIT_FAILURE, "legible_hash: malloc");

	for (x = 0; x < 20; x++)
		snprintf(&hash[x * 2], 3, "%02x", (uint8_t)hash_buffer[x]);

	hash[40] = '\0';

	return (hash);
}


/*
 * illegible_hash
 *
 * Function that converts a 40 byte human-readable SHA checksum into a 20 byte
 * binary SHA checksum.
 */

static char *
illegible_hash(char *hash_buffer)
{
	char *hash = NULL;
	int   x = 0;

	if ((hash = (char *)malloc(20)) == NULL)
		err(EXIT_FAILURE, "illegible_hash: malloc");

	for (x = 0; x < 20; x++)
		hash[x] = (char)(16 * (hash_buffer[x * 2] -
			(hash_buffer[x * 2] > 58 ? 87 : 48)) +
			hash_buffer[x * 2 + 1] -
			(hash_buffer[x * 2 + 1] > 58 ? 87 : 48));

	return (hash);
}


/*
 * ignore_file
 *
 * Function that returns true if the path is in the set of "ignores".
 */

static bool
ignore_file(connector *session, char *path, uint8_t flag)
{
	int              x, code;
	bool             ignore = false;
	struct file_node find;

	if (flag == IGNORE_FORCE_READ) {
		/* Files currently in the repository cannot be ignored. */

		find.path = path;

		if (RB_FIND(Tree_Remote_Path, &Remote_Path, &find))
			return (false);

		/* Files in the sys/arch/conf directories must be read. */

		if ((strstr(path, "/sys/")) && (strstr(path, "/conf/")))
			return (false);
	}

	/* Check the list of ignores. */

	for (x = 0; x < session->ignores; x++) {
		code = regexec(session->ignore[x]->pattern, path, 0, NULL, 0);

		if (code == 0) {
			ignore = (session->ignore[x]->negate ? false : true);
		} else if (code != REG_NOMATCH)
			warnx("! ignore_file error: %s (error code %d)\n",
			path,
			code);
	}

	if ((ignore) && (session->verbosity > 1))
		fprintf(stderr, " | Ignoring %s\n", path);

	return (ignore);
}


/*
 * new_file_node
 *
 * Function that creates a new file node.
 */

static struct file_node *
new_file_node(char *path, mode_t mode, char *hash, bool keep, bool save)
{
	struct file_node *new_node = NULL;

	new_node = (struct file_node *)malloc(sizeof(struct file_node));

	if (new_node == NULL)
		err(EXIT_FAILURE, "new_file_node: malloc");

	new_node->mode = mode;
	new_node->hash = hash;
	new_node->path = path;
	new_node->keep = keep;
	new_node->save = save;

	return (new_node);
}


/*
 * make_path
 *
 * Procedure that creates a directory and all intermediate directories if they
 * do not exist.
 */

static void
make_path(char *path, mode_t mode)
{
	char *temp = path;

	if (mkdir(path, mode) == -1) {
		if ((errno != ENOENT) && (errno != EEXIST))
			err(EXIT_FAILURE, "make_path: cannot create %s", path);

		/* Create any missing intermediate directories. */

		while ((temp = strchr(temp, '/')) != NULL) {
			if (temp != path) {
				*temp = '\0';

				if ((!path_exists(path))
					&& (mkdir(path, mode) == -1)
					&& (errno != EEXIST))
						err(EXIT_FAILURE,
							"make_path: "
							"cannot create %s",
							path);

				*temp = '/';
			}

			temp++;
		}

	/* Create the target directory. */

	if ((mkdir(path, mode) == -1) && (errno != EEXIST))
		err(EXIT_FAILURE, "make_path: cannot create %s", path);
	}
}


/*
 * absolute_path
 *
 * Procedure that ensures the new path is an absolute path.
 */

static char *
absolute_path(char *new_path)
{
	char   path[BUFFER_4K], *current_path = NULL;
	size_t path_length = 0;

	current_path = getwd(NULL);
	path[0]      = '\0';
	path_length  = strlen(new_path);

	/* If the new path is absolute, use it. */

	if (path_length && new_path[0] == '/')
		snprintf(path, BUFFER_4K, "%s", new_path);

	/* If the new path is relative, append it to the current path. */

	if (path_length > 1 && new_path[0] == '.' && new_path[1] == '/')
		snprintf(path, BUFFER_4K, "%s%s", current_path, new_path + 1);

	if (path_length && new_path[0] != '/' && new_path[0] != '.')
		snprintf(path, BUFFER_4K, "%s/%s", current_path, new_path);

	/* Reject paths that traverse. */

	if (path_length > 2 && strnstr(new_path, "../", path_length) != NULL)
		errc(EXIT_FAILURE, EACCES,
			"absolute_path: illegal path traverse in %s",
			new_path);

	/* Remove any trailing slashes. */

	path_length = strlen(path);

	while (path_length && path[path_length - 1] == '/')
		path[--path_length] = '\0';

	/* Return the new path. */

	free(current_path);

	return (strdup(path));
}


/*
 * prune_tree
 *
 * Procedure that recursively removes a directory.
 */

static bool
prune_tree(connector *session, char *base_path)
{
	DIR           *directory = NULL;
	struct dirent *entry = NULL;
	struct stat    sb;
	char           full_path[strlen(base_path) + 1 + MAXNAMLEN + 1];
	size_t         length;
	bool           pruned = true;

	/* Sanity check the directory to prune. */

	length = strlen(session->path_target);

	if (strnstr(base_path, session->path_target, length) != base_path)
		errc(EXIT_FAILURE, EACCES,
			"prune_tree: %s is not located in the %s tree",
			base_path,
			session->path_target);

	if (strnstr(base_path, "../", strlen(base_path)) != NULL)
		errc(EXIT_FAILURE, EACCES,
			"prune_tree: illegal path traverse in %s",
			base_path);

	/* Remove the directory contents. */

	if ((directory = opendir(base_path)) == NULL)
		return pruned;

	while ((entry = readdir(directory)) != NULL) {
		snprintf(full_path, sizeof(full_path),
			"%s/%s",
			base_path,
			entry->d_name);

		if (lstat(full_path, &sb) != 0)
			err(EXIT_FAILURE,
				"prune_tree: cannot stat() %s",
				full_path);

		if (ignore_file(session, full_path, IGNORE_SKIP_DELETE)) {
			pruned = false;
			continue;
		}

		if (S_ISDIR(sb.st_mode) != 0) {
			if (entry->d_namlen == 1)
				if (strcmp(entry->d_name, "." ) == 0)
					continue;

			if (entry->d_namlen == 2)
				if (strcmp(entry->d_name, "..") == 0)
					continue;

			if (!prune_tree(session, full_path))
				pruned = false;
		} else {
			if (remove(full_path) == -1)
				err(EXIT_FAILURE,
					"prune_tree: cannot remove %s",
					full_path);
		}
	}

	closedir(directory);

	if (pruned && rmdir(base_path) != 0)
		fprintf(stderr, " ! cannot remove %s\n", base_path);

	return pruned;
}


/*
 * path_exists
 *
 * Function wrapper for stat that checks to see if a path exists.
 */

static bool
path_exists(const char *path)
{
	struct stat check;

	return (stat(path, &check) == 0 ? true : false);

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
		if (file.st_size > (off_t)*buffer_size) {
			*buffer_size = (uint32_t)file.st_size;
			*buffer = (char *)realloc(*buffer, *buffer_size + 1);

			if (buffer == NULL)
				err(EXIT_FAILURE, "load_file: malloc");
		}

		if ((fd = open(path, O_RDONLY)) == -1)
			err(EXIT_FAILURE, "load_file: cannot read %s", path);

		if ((off_t)read(fd, *buffer, *buffer_size) != file.st_size)
			errc(EXIT_FAILURE, EIO,
				"load_file: problem reading %s",
				path);

		close(fd);

		*(*buffer + *buffer_size) = '\0';
	}
}


/*
 * trim_path
 *
 * Procedure that trims a path to the specified display depth.
 */

static char *
trim_path(char *path, int display_depth, bool *just_added)
{
	struct file_node *new_node = NULL, find;
	int               x = -1;
	char             *trim = NULL, *trimmed_path = NULL;

	trimmed_path = strdup(path);

	if (display_depth == 0)
		return (trimmed_path);

	trim = trimmed_path;

	while ((x++ < display_depth) && (trim != NULL))
		trim = strchr(trim + 1, '/');

	if (trim)
		*trim = '\0';

	find.path = trimmed_path;

	if (!RB_FIND(Tree_Trim_Path, &Trim_Path, &find)) {
		new_node = new_file_node(
			strdup(trimmed_path),
			0,
			NULL,
			false,
			false);

		RB_INSERT(Tree_Trim_Path, &Trim_Path, new_node);
		*just_added = true;
	} else {
		*just_added = false;
	}

	return (trimmed_path);
}


/*
 * save_file
 *
 * Procedure that saves a blob/file.
 */

static void
save_file(char *path, mode_t mode, char *buffer, uint64_t buffer_size,
          int verbosity, int display_depth)
{
	struct stat check;

	char temp_buffer[buffer_size + 1], *trim = NULL, *display_path = NULL;
	int  fd;
	bool exists = false, just_added = false;

	display_path = trim_path(path, display_depth, &just_added);

	/* Create the directory, if needed. */

	if ((trim = strrchr(path, '/')) != NULL) {
		*trim = '\0';

		exists = (stat(path, &check) == 0 ? true : false);

		if (exists && !S_ISDIR(check.st_mode))
			if (unlink(path) == 0)
				exists = false;

		if (!exists)
			make_path(path, 0755);

		*trim = '/';
	}

	/* Print the file or trimmed path. */

	if (verbosity > 0) {
		exists = path_exists(path);

		if ((display_depth == 0) || (just_added))
			printf(" %c %s\n", (exists ? '*' : '+'), display_path);
	}

	free(display_path);

	if (S_ISLNK(mode)) {
		/*
		 * Make sure the buffer is null terminated, then save it as the
		 * file to link to.
		 */

		memcpy(temp_buffer, buffer, buffer_size);
		temp_buffer[buffer_size] = '\0';

		if (symlink(temp_buffer, path) == -1 &&
		    (unlink(path), symlink(temp_buffer, path) == -1))
			err(EXIT_FAILURE,
				"save_file: symlink failure %s -> %s",
				path,
				temp_buffer);
	} else {
		exists = (stat(path, &check) == 0 ? true : false);

		/* If the path exists, make sure the permissions are intact. */

		if (exists)
			chmod(path, mode);

		fd = open(path, O_WRONLY | O_CREAT | O_TRUNC);

		if ((fd == -1) && (errno != EEXIST))
			err(EXIT_FAILURE,
				"save_file: write file failure %s",
				path);

		chmod(path, mode);
		write(fd, buffer, buffer_size);
		close(fd);
	}
}


/*
 * calculate_object_hash
 *
 * Function that adds Git's "type file-size\0" header to a buffer and returns
 * the SHA checksum.
 */

static char *
calculate_object_hash(char *buffer, uint32_t buffer_size, int type)
{
	uint64_t    digits = buffer_size;
	size_t      header_width = 0;
	char       *hash = NULL, *hash_buffer = NULL, *temp_buffer = NULL;
	const char *types[8] = {
		"", "commit", "tree", "blob", "tag",
		"", "ofs-delta", "ref-delta"
		};

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

	SHA1((uint8_t *)temp_buffer,
		buffer_size + header_width,
		(uint8_t *)hash_buffer);

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
calculate_file_hash(char *path, mode_t file_mode)
{
	char     *buffer = NULL, *hash = NULL, temp_path[BUFFER_4K];
	uint32_t  buffer_size = 0;
	ssize_t   bytes_read = 0;

	if (S_ISLNK(file_mode)) {
		bytes_read = readlink(path, temp_path, BUFFER_4K);
		temp_path[bytes_read] = '\0';

		hash = calculate_object_hash(
			temp_path,
			(uint32_t)strlen(temp_path),
			3);
	} else {
		load_file(path, &buffer, &buffer_size);
		hash = calculate_object_hash(buffer, buffer_size, 3);
		free(buffer);
	}

	return (hash);
}


/*
 * append
 *
 * Procedure that appends one string to another.
 */

static void
append(char **buffer, uint32_t *buffer_size, const char *addendum,
       size_t addendum_size)
{
	*buffer = (char *)realloc(*buffer, *buffer_size + addendum_size + 1);

	if (*buffer == NULL)
		err(EXIT_FAILURE, "append: realloc");

	memcpy(*buffer + *buffer_size, addendum, addendum_size);
	*buffer_size += addendum_size;
	*(*buffer + *buffer_size) = '\0';
}


/*
 * extend_updating_list
 *
 * Procedure that adds the path of an UPDATING file to a string.
 */

static void
extend_updating_list(connector *session, char *path)
{
	uint32_t size;
	char     temp[BUFFER_4K];

	size = (session->updating ? (uint32_t)strlen(session->updating) : 0);

	snprintf(temp, sizeof(temp), "#\t%s\n", path);
	append(&session->updating, &size, temp, strlen(temp));
}


/*
 * load_remote_data
 *
 * Procedure that loads the list of remote data and checksums, if it exists.
 */

static void
load_remote_data(connector *session)
{
	struct file_node *file = NULL;
	char     *buffer = NULL, *hash = NULL, *temp_hash = NULL;
	char     *line = NULL, *raw = NULL, *path = NULL, *data = NULL;
	char      temp[BUFFER_4K], base_path[BUFFER_4K], item[BUFFER_4K];
	uint32_t  count = 0, buffer_size = 0, data_size = 0;
	size_t    item_length = 0;

	load_file(session->remote_data_file, &data, &data_size);
	raw = data;

	while ((line = strsep(&raw, "\n"))) {
		/* The first line stores the "have". */

		if (count++ == 0) {
			session->have = strdup(line);
			continue;
		}

		/*
		 * Empty lines signify the end of a directory entry, so create
		 * an obj_tree for what has been read.
		 */

		if (strlen(line) == 0) {
			if (buffer != NULL) {
				if (session->clone == false)
					store_object(session,
						2,
						buffer,
						buffer_size,
						0,
						0,
						NULL);

				buffer = NULL;
				buffer_size = 0;
			}

			continue;
		}

		/* Split the line. */

		hash = strchr(line,     '\t');
		path = strchr(hash + 1, '\t');

		if ((hash == NULL) || (path == NULL)) {
			fprintf(stderr,
				" ! Malformed line '%s' in %s.  Skipping...\n",
				line,
				session->remote_data_file);

			continue;
		} else {
			hash++;
			path++;
		}

		*(hash -  1) = '\0';
		*(hash + 40) = '\0';

		/* Store the file data. */

		file = new_file_node(
			NULL,
			(mode_t)strtol(line, (char **)NULL, 8),
			strdup(hash),
			false,
			false);

		if (path[strlen(path) - 1] == '/') {
			snprintf(base_path, sizeof(base_path), "%s", path);
			snprintf(temp, sizeof(temp), "%s", path);
			temp[strlen(path) - 1] = '\0';
		} else {
			snprintf(temp, sizeof(temp), "%s%s", base_path, path);

			temp_hash = illegible_hash(hash);

			/*
			 * Build the item and add it to the buffer that will
			 * become the obj_tree for this directory.
			 */

			snprintf(item, sizeof(item) - 22, "%s %s", line, path);
			item_length = strlen(item);
			memcpy(item + item_length + 1, temp_hash, 20);
			item_length += 21;
			item[item_length] = '\0';

			append(&buffer, &buffer_size, item, item_length);

			free(temp_hash);
		}

		file->path = strdup(temp);

		RB_INSERT(Tree_Remote_Path, &Remote_Path, file);
	}

	/* Load the commit history. */

	if (!path_exists(session->remote_history_file))
		return;

	load_file(session->remote_history_file, &data, &data_size);
	raw = data;

	while ((line = strsep(&raw, "\n"))) {
		if (strlen(line) == 0)
			continue;

		hash = strchr(line, ' ');

		if (hash) {
			*hash = '\0';
			*(hash + 41) = '\0';

/*			insert_commit_node(strdup(hash), line); */
		}
	}

	free(data);
}


/*
 * scan_local_repository
 *
 * Procedure that recursively finds and adds local files and directories to
 * separate red-black trees.
 */

static void
scan_local_repository(connector *session, char *base_path)
{
	DIR              *directory = NULL;
	struct stat       file;
	struct dirent    *entry = NULL;
	struct file_node *new_node = NULL, find, *found = NULL;
	char             *path = NULL, file_hash[20], *keep = NULL;
	unsigned long     path_length = 0;

	/* Make sure the base path exists in the remote data list. */

	find.path = base_path;
	found     = RB_FIND(Tree_Remote_Path, &Remote_Path, &find);

	/* Add the base path to the local trees. */

	new_node = new_file_node(
		strdup(base_path),
		(found ? found->mode : 040000),
		(found ? strdup(found->hash) : NULL),
		(strlen(base_path) == strlen(session->path_target)),
		false);

	RB_INSERT(Tree_Local_Path, &Local_Path, new_node);

	if (found)
		RB_INSERT(Tree_Local_Hash, &Local_Hash, new_node);

	/* Process the directory's contents. */

	if (stat(base_path, &file) == -1)
		return;

	if ((directory = opendir(base_path)) == NULL)
		return;

	while ((entry = readdir(directory)) != NULL) {
		if ((entry->d_namlen == 1) && (!strcmp(entry->d_name, "." )))
			continue;

		if ((entry->d_namlen == 2) && (!strcmp(entry->d_name, "..")))
			continue;

		path_length = strlen(base_path) + entry->d_namlen + 2;
		path        = (char *)malloc(path_length + 1);

		if (path == NULL)
			err(EXIT_FAILURE,
				"scan_local_repository: malloc");

		snprintf(path, path_length, "%s/%s", base_path, entry->d_name);

		if (lstat(path, &file) == -1)
			err(EXIT_FAILURE,
				"scan_local_repository: cannot read %s",
				path);

		if (S_ISDIR(file.st_mode)) {
			scan_local_repository(session, path);
			free(path);
		} else {
			keep = strnstr(path, ".gituprevision", path_length);

			new_node = new_file_node(
				path,
				file.st_mode,
				NULL,
				(keep != NULL ? true : false),
				false);

			if (ignore_file(session, path, IGNORE_FORCE_READ)) {
				new_node->hash = (char *)malloc(20);

				if (new_node->hash == NULL)
					err(EXIT_FAILURE,
						"scan_local_repository: "
						"malloc");

				SHA1((uint8_t *)path,
					path_length,
					(uint8_t *)file_hash);

				memcpy(new_node->hash, file_hash, 20);
			} else
				new_node->hash = calculate_file_hash(
					path,
					file.st_mode);

			RB_INSERT(Tree_Local_Hash, &Local_Hash, new_node);
			RB_INSERT(Tree_Local_Path, &Local_Path, new_node);
		}
	}

	closedir(directory);
}


/*
 * load_object
 *
 * Procedure that loads a local file and adds it to the array/tree of pack
 * file objects.
 */

static void
load_object(connector *session, char *hash, char *path)
{
	struct object_node  lookup_object;
	struct file_node   *find = NULL, lookup_file;
	char               *buffer = NULL;
	uint32_t            buffer_size = 0;

	lookup_object.hash = hash;
	lookup_file.hash   = hash;
	lookup_file.path   = path;

	/*
	 * If the object does not exist, look for it first by hash, then by path
	 * and if it is found and the SHA checksum references a file, load it
	 * and store it.
	 */

	if (RB_FIND(Tree_Objects, &Objects, &lookup_object) != NULL)
		return;

	find = RB_FIND(Tree_Local_Hash, &Local_Hash, &lookup_file);

	if ((find == NULL) && (path != NULL))
		find = RB_FIND(Tree_Local_Path, &Local_Path, &lookup_file);

	if (find) {
		if (!S_ISDIR(find->mode)) {
			load_file(find->path, &buffer, &buffer_size);

			store_object(session,
				3,
				buffer,
				buffer_size,
				0,
				0,
				NULL);
		}
	} else {
		errc(EXIT_FAILURE, ENOENT,
			"load_object: local file for object %s -- %s not found",
			hash,
			path);
	}
}


/*
 * create_tunnel
 *
 * Procedure that sends a CONNECT command to create a proxy tunnel.
 */

static void
create_tunnel(connector *session)
{
	char command[BUFFER_4K];

	snprintf(command, BUFFER_4K,
		"CONNECT %s:%d HTTP/1.1\r\n"
		"Host: %s:%d\r\n"
		"%s"
		"\r\n",
		session->host_bracketed,
		session->port,
		session->host_bracketed,
		session->port,
		session->proxy_credentials);

		process_command(session, command);
}


/*
 * connect_server
 *
 * Procedure that establishes a connection with the server.
 */

static void
connect_server(connector *session)
{
	struct addrinfo hints, *start = NULL, *tmp = NULL, *local = NULL;
	struct timeval  timeout;
	int             sd = 0, error = 0, option = 1;
	socklen_t       size = 0;
	char            type[10], *host = NULL;

	/* Get addrinfo for local address. */

	if (session->source_address) {
		bzero(&hints, sizeof(struct addrinfo));
		hints.ai_socktype = SOCK_STREAM;
		hints.ai_flags    = AI_ADDRCONFIG | AI_PASSIVE;

		error = getaddrinfo(session->source_address,
			0,
			&hints,
			&local);

		if (error)
			errx(EXIT_FAILURE,
				"connect_server: getaddrinfo failure: %s",
				gai_strerror(error));
	}

	/* Get addrinfo for remote address. */

	host = (session->proxy_host ? session->proxy_host : session->host);

	snprintf(type, sizeof(type),
		"%d",
		(session->proxy_host ? session->proxy_port : session->port));

	bzero(&hints, sizeof(struct addrinfo));
	hints.ai_family   = AF_UNSPEC;
	hints.ai_socktype = SOCK_STREAM;
	hints.ai_protocol = IPPROTO_TCP;

	if ((error = getaddrinfo(host, type, &hints, &start)))
		errx(EXIT_FAILURE,
			"connect_server: getaddrinfo failure: %s",
			gai_strerror(error));

	/* Open the socket. */

	for (tmp = start; tmp != NULL; tmp = tmp->ai_next) {
		sd = socket(tmp->ai_family, tmp->ai_socktype, tmp->ai_protocol);

		if (sd < 0)
			/* trying each addr returned, cont. with next in list */
			continue;

		if ((local) && (bind(sd, local->ai_addr, local->ai_addrlen)))
			err(EXIT_FAILURE, "connect_server: bind failure");

		if (connect(sd, tmp->ai_addr, tmp->ai_addrlen) != -1)
			break;
		else
			close(sd);
	}

	freeaddrinfo(start);
	freeaddrinfo(local);

	if (tmp == NULL)
		err(EXIT_FAILURE, "connect_server: connect failure");

	/* Set the socket options. */

	if (setsockopt(sd, SOL_SOCKET, SO_KEEPALIVE, &option, sizeof(int)))
		err(EXIT_FAILURE, "setup_ssl: setsockopt SO_KEEPALIVE");

	option = BUFFER_1M;

	if (setsockopt(sd, SOL_SOCKET, SO_SNDBUF, &option, sizeof(int)))
		err(EXIT_FAILURE, "setup_ssl: setsockopt SO_SNDBUF");

	if (setsockopt(sd, SOL_SOCKET, SO_RCVBUF, &option, sizeof(int)))
		err(EXIT_FAILURE, "setup_ssl: setsockopt SO_RCVBUF");

	size = sizeof(struct timeval);
	bzero(&timeout, size);
	timeout.tv_sec = 300;

	if (setsockopt(sd, SOL_SOCKET, SO_RCVTIMEO, &timeout, size))
		err(EXIT_FAILURE, "setup_ssl: setsockopt SO_RCVTIMEO");

	if (setsockopt(sd, SOL_SOCKET, SO_SNDTIMEO, &timeout, size))
		err(EXIT_FAILURE, "setup_ssl: setsockopt SO_SNDTIMEO");

	session->socket_descriptor = sd;
}


/*
 * setup_ssl
 *
 * Procedure that sends a command to the server and processes the response.
 */

static void
setup_ssl(connector *session)
{
	int error = 0;

	SSL_library_init();
	SSL_load_error_strings();
	session->ctx = SSL_CTX_new(SSLv23_client_method());
	SSL_CTX_set_mode(session->ctx, SSL_MODE_AUTO_RETRY);
	SSL_CTX_set_options(session->ctx, SSL_OP_ALL | SSL_OP_NO_TICKET);

	if ((session->ssl = SSL_new(session->ctx)) == NULL)
		err(EXIT_FAILURE, "setup_ssl: SSL_new");

	SSL_set_fd(session->ssl, session->socket_descriptor);

	while ((error = SSL_connect(session->ssl)) == -1)
		fprintf(stderr,
			"setup_ssl: SSL_connect error: %d\n",
			SSL_get_error(session->ssl, error));
}


/*
 * process_command
 *
 * Procedure that sends a command to the server and processes the response.
 */

static void
process_command(connector *session, char *command)
{
	char     read_buffer[BUFFER_4K], *temp = NULL;
	char    *marker_start = NULL, *marker_end = NULL, *data_start = NULL;
	long     chunk_size = -1, response_code = 0;
	ssize_t  marker_offset = 0, data_start_offset = 0;
	ssize_t  bytes_read = 0, bytes_sent = 0, bytes_to_send = 0;
	ssize_t  total_bytes_read = 0, total_bytes_sent = 0;
	ssize_t  bytes_to_move = 0, bytes_expected = 0, check_bytes = 0;
	int      error = 0, outlen = 0;
	bool     ok = false, chunked_transfer = true;


	bytes_to_send = (ssize_t)strlen(command);

	if (session->verbosity > 2)
		fprintf(stderr, "%s\n\n", command);

	/* Transmit the command to the server. */

	while (total_bytes_sent < bytes_to_send) {
		if (session->ssl)
			bytes_sent = SSL_write(
				session->ssl,
				command + total_bytes_sent,
				(int)(bytes_to_send - total_bytes_sent));
		else
			bytes_sent = write(
				session->socket_descriptor,
				command + total_bytes_sent,
				(size_t)(bytes_to_send - total_bytes_sent));

		if (bytes_sent <= 0) {
			if (bytes_sent < 0 && (errno == EINTR || errno == 0))
				continue;
			else
				err(EXIT_FAILURE, "process_command: send");
		}

		total_bytes_sent += bytes_sent;

		if (session->verbosity > 2)
			fprintf(stderr,
				"\r==> bytes sent: %ld",
				(long)total_bytes_sent);
	}

	if (session->verbosity > 2)
		fprintf(stderr, "\n");

	/* Process the response. */

	while (chunk_size) {
		if (session->ssl)
			bytes_read = SSL_read(
				session->ssl,
				read_buffer,
				BUFFER_4K);
		else
			bytes_read = read(
				session->socket_descriptor,
				read_buffer,
				BUFFER_4K);

		if (bytes_read == 0)
			break;

		if (bytes_read < 0)
			err(EXIT_FAILURE,
				"process_command: SSL_read error: %d",
				SSL_get_error(session->ssl, error));

		/*
		 * Expand the buffer if needed, preserving the position and
		 * data_start if the buffer moves.
		 */

		unsigned long temp_total = total_bytes_read + bytes_read + 1;

		if (temp_total > session->response_blocks * BUFFER_1M) {
			marker_offset     = marker_start - session->response;
			data_start_offset = data_start   - session->response;

			session->response = (char *)realloc(
				session->response,
				++session->response_blocks * BUFFER_1M);

			if (session->response == NULL)
				err(EXIT_FAILURE, "process_command: realloc");

			marker_start = session->response + marker_offset;
			data_start   = session->response + data_start_offset;
		}

		/* Add the bytes received to the buffer. */

		memcpy(session->response + total_bytes_read,
			read_buffer,
			(unsigned long)bytes_read);

		total_bytes_read += bytes_read;
		session->response[total_bytes_read] = '\0';

		if (session->verbosity > 2)
			fprintf(stderr, "\r==> "
				"bytes read: %zd\t"
				"bytes_expected: %ld\t"
				"total_bytes_read: %ld",
				bytes_read,
				(long)bytes_expected,
				(long)total_bytes_read);

		while ((session->verbosity) && (isatty(STDERR_FILENO))) {
			struct timespec now;
			static struct   timespec then;
			char            buf[80], htotalb[7], persec[8];
			static ssize_t  last_total;
			static double   sum;
			double          secs, speed;

			if (clock_gettime(CLOCK_MONOTONIC_FAST, &now) == -1)
				err(EXIT_FAILURE,
					"process_command: clock_gettime");

			if (then.tv_sec == 0)
				then = now, secs = 1, sum = 1;
			else {
				secs = (double)(now.tv_sec - then.tv_sec) +
					(double)(now.tv_nsec - then.tv_nsec)
						* 1e-9;

				if (1 > secs)
					break;
				else
					sum += secs;
			}

			speed = (double)(total_bytes_read - last_total) / secs;

			humanize_number(htotalb, sizeof(htotalb),
				total_bytes_read,
				"B",
				HN_AUTOSCALE,
				HN_DECIMAL | HN_DIVISOR_1000);

			humanize_number(persec, sizeof(persec),
				(int64_t)speed,
				"B",
				HN_AUTOSCALE,
				HN_DECIMAL | HN_DIVISOR_1000);

			snprintf(buf, sizeof(buf) - 1,
				"  %s in %dm%02ds, %s/s now",
				htotalb,
				(int)(sum / 60),
				(int)sum % 60,
				persec);

			if (isatty(STDERR_FILENO))
				outlen = fprintf(stderr, "%-*s\r",
					outlen,
					buf) - 1;

			last_total = total_bytes_read;
			then       = now;
			break;
		}

		/* Find the boundary between the header and the data. */

		if (chunk_size == -1) {
			marker_start = strnstr(session->response,
				"\r\n\r\n",
				(size_t)total_bytes_read);

			if (marker_start == NULL) {
				continue;
			} else {
				bytes_expected = marker_start
					- session->response
					+ 4;
				marker_start += 2;
				data_start = marker_start;

				/* Check the response code. */

				if (strstr(session->response, "HTTP/1.") ==
					session->response) {
					response_code = strtol(
						strchr(session->response, ' ')
						+ 1,
						(char **)NULL, 10);

					if (response_code == 200)
						ok = true;

					if ((session->proxy_host)
						&& (response_code >= 200)
						&& (response_code < 300))
						ok = true;
				}

				temp = strstr(
					session->response,
					"Content-Length: ");

				if (temp != NULL) {
					bytes_expected += (ssize_t)strtol(
						temp + 16,
						(char **)NULL, 10);

					chunk_size = -2;
					chunked_transfer = false;
				}
			}
		}

		/* Successful CONNECT responses do not contain a body. */

		if ((strstr(command, "CONNECT ") == command) && (ok))
			break;

		if ((!chunked_transfer)
			&& (total_bytes_read < bytes_expected))
			continue;

		while ((chunked_transfer)
			&& (total_bytes_read + chunk_size > bytes_expected)) {
			/* Make sure the whole chunk marker has been read. */

			check_bytes = (ssize_t)(total_bytes_read
				- (marker_start + 2 - session->response));

			if (check_bytes < 0)
				break;

			marker_end = strnstr(
				marker_start + 2,
				"\r\n",
				(size_t)check_bytes);

			if (marker_end == NULL)
				break;

			/* Remove the chunk length marker. */

			chunk_size    = strtol(marker_start, (char **)NULL, 16);
			bytes_to_move = (ssize_t)(total_bytes_read
				- (marker_end + 2 - session->response) + 1);

			if (bytes_to_move < 0)
				break;

			memmove(marker_start,
				marker_end + 2,
				(size_t)bytes_to_move);

			total_bytes_read -= (marker_end + 2 - marker_start);

			if (chunk_size == 0)
				break;

			marker_start   += (unsigned)chunk_size;
			bytes_expected += (unsigned)chunk_size;
		}
	}

	if ((session->verbosity) && (isatty(STDERR_FILENO)))
		fprintf(stderr, "\r\e[0K\r");

	if (!ok)
		errc(EXIT_FAILURE, EINVAL,
			"process_command: read failure:\n%s\n",
			session->response);

	/* Remove the header. */

	session->response_size = (uint32_t)(total_bytes_read
		- (data_start - session->response));

	memmove(session->response, data_start, session->response_size);
	session->response[session->response_size] = '\0';
}


/*
 * send_command
 *
 * Function that constructs the command to the fetch the full pack data.
 */

static void
send_command(connector *session, char *want)
{
	char   *command = NULL;
	size_t  want_size = 0;

	want_size = strlen(want);

	if ((command = (char *)malloc(BUFFER_4K + want_size)) == NULL)
		err(EXIT_FAILURE, "send_command: malloc");

	snprintf(command, BUFFER_4K + want_size,
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
		session->repository_path,
		session->host_bracketed,
		session->port,
		GITUP_VERSION,
		want_size,
		want);

	process_command(session, command);

	free(command);
}


/*
 * build_clone_command
 *
 * Function that constructs and executes the command to the fetch the shallow
 * pack data.
 */

static char *
build_clone_command(connector *session)
{
	char *command = NULL;

	if ((command = (char *)malloc(BUFFER_4K)) == NULL)
		err(EXIT_FAILURE, "build_clone_command: malloc");

	snprintf(command, BUFFER_4K,
		"0011command=fetch0001"
		"000fno-progress"
		"000dofs-delta"
		"0034shallow %s"
		"0032want %s\n"
		"0009done\n0000",
		session->want,
		session->want);

	return (command);
}


/*
 * build_commit_command
 *
 * Function that constructs and executes the command to the fetch the commit
 * data.
 */

static char *
build_commit_command(connector *session)
{
	char *command = NULL, temp[64];
	bool  have = false;

	if ((command = (char *)malloc(BUFFER_4K)) == NULL)
		err(EXIT_FAILURE, "build_commit_command: malloc");

	if (session->have)
		have = true;

	if (session->keep_pack_file && !path_exists(session->pack_history_file))
		have = false;

	if (!path_exists(session->remote_history_file))
		have = false;

	if (have == false)
		temp[0] = '\0';
	else
		snprintf(temp, sizeof(temp), "0032have %s\n", session->have);

	snprintf(command, BUFFER_4K,
		"0011command=fetch0001"
		"000dthin-pack"
		"000fno-progress"
		"000dofs-delta"
		"0012filter tree:0\n"
		"0032want %s\n"
		"%s"
		"0009done\n0000",
		session->want,
		temp);

	return (command);
}


/*
 * build_pull_command
 *
 * Function that constructs and executes the command to the fetch the
 * incremental pack data.
 */

static char *
build_pull_command(connector *session)
{
	char *command = NULL;

	if ((command = (char *)malloc(BUFFER_4K)) == NULL)
		err(EXIT_FAILURE, "build_pull_command: malloc");

	snprintf(command, BUFFER_4K,
		"0011command=fetch0001"
		"000dthin-pack"
		"000fno-progress"
		"000dofs-delta"
		"0034shallow %s"
		"0034shallow %s"
		"000cdeepen 1"
		"0032want %s\n"
		"0032have %s\n"
		"0009done\n0000",
		session->want,
		session->have,
		session->want,
		session->have);

	return (command);
}


/*
 * build_repair_command
 *
 * Procedure that compares the local repository tree with the data saved from
 * the last run to see if anything has been modified.
 */

static char *
build_repair_command(connector *session)
{
	struct file_node *find = NULL, *found = NULL;
	char             *command = NULL, *want = NULL, line[BUFFER_4K];
	const char       *message[2] = { "is missing.", "has been modified." };
	uint32_t          want_size = 0;

	RB_FOREACH(find, Tree_Remote_Path, &Remote_Path) {
		found = RB_FIND(Tree_Local_Path, &Local_Path, find);

		if (found == NULL ||
			(strncmp(found->hash, find->hash, 40) != 0 &&
			!ignore_file(session, find->path, IGNORE_FORCE_READ))) {

			if (session->verbosity)
				fprintf(stderr,
					" ! %s %s\n",
					find->path,
					message[found ? 1 : 0]);

			snprintf(line, sizeof(line),
				"0032want %s\n",
				find->hash);

			append(&want, &want_size, line, strlen(line));
		}
	}

	if (want_size == 0)
		return (NULL);

	if (want_size > 3276800)
		errc(EXIT_FAILURE, E2BIG,
			"build_repair_command: There are too many files to "
			"repair -- please re-clone the repository");

	if ((command = (char *)malloc(BUFFER_4K + want_size)) == NULL)
		err(EXIT_FAILURE, "build_repair_command: malloc");

	snprintf(command, BUFFER_4K + want_size,
		"0011command=fetch0001"
		"000dthin-pack"
		"000fno-progress"
		"000dofs-delta"
		"%s"
		"000cdeepen 1"
		"0009done\n0000",
		want);

	free(want);

	return (command);
}


/*
 * get_commit_details
 */

static void
get_commit_details(connector *session)
{
	char           command[BUFFER_4K], ref[BUFFER_4K], want[41];
	char           peeled[BUFFER_4K];
	char          *position = NULL;
	time_t         current;
	struct tm      now;
	int            tries = 2, year = 0, quarter = 0;
	unsigned long  length = 0;
	bool           detached = (session->want != NULL ? true : false);

	/* Send the initial info/refs command. */

	snprintf(command, BUFFER_4K,
		"GET %s/info/refs?service=git-upload-pack HTTP/1.1\r\n"
		"Host: %s:%d\r\n"
		"User-Agent: gitup/%s\r\n"
		"Git-Protocol: version=2\r\n"
		"\r\n",
		session->repository_path,
		session->host_bracketed,
		session->port,
		GITUP_VERSION);

	process_command(session, command);

	if (session->verbosity > 2)
		printf("%s\n", session->response);

	/* Make sure the server supports the version 2 protocol. */

	position = strnstr(session->response,
		"version 2",
		session->response_size);

	if (position == NULL)
		errc(EXIT_FAILURE, EPROTONOSUPPORT,
			"%s does not support the version 2 wire protocol",
			session->host);

	position = strnstr(session->response, "filter", session->response_size);

	if (position == NULL && session->commit_history) {
/*
		fprintf(stderr,
			"! %s does not support the filter feature and the "
			"commit history is unavailable\n",
			session->host);
*/
		session->commit_history = false;
	}

	/* Fetch the list of refs. */

	snprintf(command, BUFFER_4K,
		"0014command=ls-refs\n"
		"0016object-format=sha1"
		"0001"
		"0009peel\n"
		"000csymrefs\n"
		"0014ref-prefix HEAD\n"
		"001bref-prefix refs/heads/\n"
		"001aref-prefix refs/tags/\n"
		"0000");

	send_command(session, command);

	if (session->verbosity > 2)
		printf("%s\n", session->response);

	/* Extract the "want" checksum. */

	want[0] = '\0';

	while ((tries-- > 0) && (want[0] == '\0') && (detached == false)) {
		if (strncmp(session->branch, "quarterly", 9) == 0) {
			/*
			 * If the current calendar quarter does not exist, try
			 * the previous one.
			 */

			current = time(NULL);
			now     = *localtime(&current);
			year    = 1900 + now.tm_year
				+ ((tries == 0) && (now.tm_mon < 3) ? -1 : 0);
			quarter = ((now.tm_mon / 3)
				+ (tries == 0 ? 3 : 0)) % 4 + 1;

			snprintf(ref, BUFFER_4K,
				" refs/heads/%04dQ%d",
				year,
				quarter);
		} else if (session->tag != NULL) {
			snprintf(ref, BUFFER_4K,
				" refs/tags/%s",
				session->tag);
		} else {
			snprintf(ref, BUFFER_4K,
				" refs/heads/%s",
				session->branch);
		}

		/*
		 * Look for the "want" in peeled references first, then look
		 * before the ref.
		 */

		snprintf(peeled, sizeof(peeled), "%s peeled:", ref);

		if ((position = strstr(session->response, peeled)) != NULL)
			memcpy(want, position + strlen(peeled), 40);
		else if ((position = strstr(session->response, ref)) != NULL)
			memcpy(want, position - 40, 40);
		else if (tries == 0)
			errc(EXIT_FAILURE, EINVAL,
				"get_commit_details:%s does not exist in %s",
				ref,
				session->repository_path);
	}

	/* Retain the name of the quarterly branch being used. */

	if (strncmp(session->branch, "quarterly", 9) == 0) {
		free(session->branch);
		session->branch = strdup(ref + 12);
	}

	if (want[0] != '\0') {
		if (session->want == NULL)
			if ((session->want = (char *)malloc(41)) == NULL)
				err(EXIT_FAILURE, "get_commit_details: malloc");

		memcpy(session->want, want, 40);
		session->want[40] = '\0';

		if (session->verbosity)
			fprintf(stderr, "# Want: %s\n", session->want);
	}

	/*
	 * Because there is no way to lookup commit history, if a want commit
	 * is specified, change the branch to (detached).
	 */

	if (detached == true) {
		free(session->branch);
		session->branch = strdup("(detached)");
	}

	if ((session->verbosity) && (session->tag == NULL))
		fprintf(stderr, "# Branch: %s\n", session->branch);

	/* Create the pack file names. */

	if (session->keep_pack_file == true) {
		length = strlen(session->section) + 47;

		session->pack_data_file    = (char *)malloc(length + 1);
		session->pack_history_file = (char *)malloc(length + 9);

		if (session->pack_data_file == NULL)
			err(EXIT_FAILURE, "get_commit_details: malloc");

		if (session->pack_history_file == NULL)
			err(EXIT_FAILURE, "get_commit_details: malloc");

		snprintf(session->pack_data_file, length,
			"%s-%s.pack",
			session->section,
			session->want);

		snprintf(session->pack_history_file, length + 8,
			"%s.history",
			session->pack_data_file);
	}
}


/*
 * load_pack
 *
 * Procedure that loads a local copy of the pack data or fetches it from
 * the server.
 */

static void
load_pack(connector *session, char *file, bool history_file)
{
	char   hash[20], *command = NULL;
	size_t pack_size = 0;

	if ((path_exists(file)) && (session->use_pack_file)) {
		if (session->verbosity)
			fprintf(stderr, "# Loading pack file: %s\n", file);

		session->response_size = 0;

		load_file(file,
			&session->response,
			&session->response_size);
	} else {
		if (history_file)
			command = build_commit_command(session);
		else if (!session->clone)
			command = build_pull_command(session);
		else
			command = build_clone_command(session);

		fetch_pack(session, command);
	}

	pack_size = session->response_size - 20;

	/* Verify the pack data checksum. */

	SHA1((uint8_t *)session->response, pack_size, (uint8_t *)hash);

	if (memcmp(session->response + pack_size, hash, 20) != 0)
		errc(EXIT_FAILURE, EAUTH,
			"load_pack: pack checksum mismatch -- "
			"expected: %s, received: %s",
			legible_hash(session->response + pack_size),
			legible_hash(hash));

	/* Save the pack data. */

	if ((!path_exists(file)) && (session->keep_pack_file)) {
		if (session->verbosity)
			fprintf(stderr, "# Saving pack file: %s\n", file);

		save_file(file,
			0644,
			session->response,
			session->response_size,
			0,
			0);
	}

	/* Process the pack data. */

	unpack_objects(session);

	free(session->response);
	session->response        = NULL;
	session->response_size   = 0;
	session->response_blocks = 0;
}


/*
 * fetch_pack
 *
 * Procedure that fetches pack data from the server.
 */

static void
fetch_pack(connector *session, char *command)
{
	char   *pack_start = NULL, hash[20];
	long    chunk_size = 1, source = 0, target = 0;
	size_t  pack_size = 0;

	/* Request the pack data. */

	send_command(session, command);

	/* Find the start of the pack data and remove the header. */

	if ((pack_start = strstr(session->response, "PACK")) == NULL)
		errc(EXIT_FAILURE, EFTYPE,
			"fetch_pack: malformed pack data:\n%s",
			session->response);

	pack_start -= 5;

	session->response_size -= (uint64_t)(pack_start
		- session->response + 11);

	memmove(session->response, session->response + 8, 4);

	/* Remove the chunk size markers from the pack data. */

	source = pack_start - session->response;

	while (chunk_size > 0) {
		chunk_size = strtol(session->response + source,
			(char **)NULL,
			16);

		if (chunk_size == 0)
			break;

		memmove(session->response + target,
			session->response + source + 5,
			(unsigned long)chunk_size - 5);

		target += chunk_size - 5;
		source += chunk_size;
		session->response_size -= 5;
	}

	session->response_size += 5;
	pack_size = session->response_size - 20;

	/* Verify the pack data checksum. */

	SHA1((uint8_t *)session->response, pack_size, (uint8_t *)hash);

	if (memcmp(session->response + pack_size, hash, 20) != 0)
		errc(EXIT_FAILURE, EAUTH,
			"fetch_pack: pack checksum mismatch -- "
			"expected: %s, received: %s",
			legible_hash(session->response + pack_size),
			legible_hash(hash));

	/* Process the pack data. */

	unpack_objects(session);

	free(command);
}


/*
 * store_object
 *
 * Procedure that creates a new object and stores it in the array and
 * lookup tree.
 */

static void
store_object(connector *session, uint8_t type, char *buffer,
             uint32_t buffer_size, uint32_t offset_pack, uint32_t index_delta,
             char *ref_delta_hash)
{
	struct object_node *object = NULL, find;
	char               *hash = NULL, *temp = NULL, parent[41];
	bool                ok = true;

	parent[40] = '\0';

	hash = calculate_object_hash(buffer, buffer_size, type);

	/* Check to make sure the object does not already exist. */

	find.hash = hash;
	object    = RB_FIND(Tree_Objects, &Objects, &find);

	if (object != NULL && !session->repair) {
		free(hash);
	} else {
		/* Extend the array if needed, create a new node and add it. */

		if (session->objects % BUFFER_4K == 0) {
			session->object = (struct object_node **)realloc(
				session->object,
				(session->objects + BUFFER_4K)
					* sizeof(struct object_node *));

			if (session->object == NULL)
				err(EXIT_FAILURE, "store_object: realloc");
		}

		object = (struct object_node *)malloc(
			sizeof(struct object_node));

		if (object == NULL)
			err(EXIT_FAILURE, "store_object: malloc");

		object->index          = session->objects;
		object->type           = type;
		object->hash           = hash;
		object->offset_pack    = offset_pack;
		object->index_delta    = index_delta;
		object->parent         = NULL;
		object->parents        = 0;
		object->buffer         = buffer;
		object->buffer_size    = buffer_size;
		object->offset_cache   = -1;
		object->ref_delta_hash = (ref_delta_hash
			? legible_hash(ref_delta_hash)
			: NULL);

		if (session->verbosity > 2)
			fprintf(stdout,
				"###### %05d-%d\t%d\t%u\t%s\t%d\t%s\n",
				object->index,
				object->type,
				object->offset_pack,
				object->buffer_size,
				object->hash,
				object->index_delta,
				object->ref_delta_hash);

		/* Find the parent commits for commit objects. */

		if (type == 1) {
			temp = buffer;

			while ((temp + 47 - buffer < (long)buffer_size)
				&& ((temp = strstr(temp, "parent ")) != NULL)) {

				ok    = true;
				temp += 47;

				/* Make sure the commit is valid. */

				if (*temp != '\n')
					continue;

				memcpy(parent, temp - 40, 40);

				for (int x = 0; x < 40; x++)
					if (!isxdigit((uint8_t)parent[x]))
						ok = false;

				if (!ok)
					continue;

				/* Store the parent commit. */

				object->parent = (char **)realloc(
					object->parent,
					(object->parents + 1) * sizeof(char *));

				if (object->parent == NULL)
					err(EXIT_FAILURE,
						"store_object: realloc");

				object->parent[object->parents++] = strdup(
					parent);
			}
		}
/*
			char path[1024];
			int fd;

			snprintf(path, sizeof(path),
				"./temp/b%04d-%d-%s.out",
				object->index,
				object->type,
				object->hash);

			fd = open(path, O_WRONLY | O_CREAT | O_TRUNC);
			chmod(path, 0644);
			write(fd, object->buffer, object->buffer_size);
			close(fd);
*/
		if (type < 6)
			RB_INSERT(Tree_Objects, &Objects, object);

		if (session->low_memory) {
			lseek(session->cache, session->cache_length, SEEK_SET);
			write(session->cache, buffer, (size_t)buffer_size);

			object->buffer         = NULL;
			object->offset_cache   = session->cache_length;
			session->cache_length += (off_t)buffer_size;

			free(buffer);
		}

		session->object[session->objects++] = object;
	}
}


/*
 * unpack_objects
 *
 * Procedure that extracts all of the objects from the pack data.
 */

static void
unpack_objects(connector *session)
{
	unsigned long  stream_bytes = 0, x = 0;
	uint32_t       buffer_size = 0, size = 0, offset_pack = 0;
	uint32_t       index_delta = 0, lookup_offset = 0;
	uint32_t       position = 4, total_objects = 0;
	uint8_t        object_type = 0, bits = 0, mask = 0, zlib_out[16384];
	int            stream_code = 0, version = 0;
	char          *buffer = NULL, *ref_delta_hash = NULL;

	/* Check the pack version number. */

	version   = (uint8_t)session->response[position + 3];
	position += 4;

	if (version != 2)
		errc(EXIT_FAILURE, EFTYPE,
			"unpack_objects: pack version %d not supported",
			version);

	/* Determine the number of objects in the pack data. */

	for (x = 0; x < 4; x++, position++)
		total_objects = (total_objects << 8)
			+ (uint8_t)session->response[position];

	if (session->verbosity > 2)
		fprintf(stderr,
			"\nversion: %d, total_objects: %d, pack_size: %d\n\n",
			version,
			total_objects,
			session->response_size);

	/* Unpack the objects. */

	while ((position < session->response_size) && (total_objects-- > 0)) {
		offset_pack    = position;
		index_delta    = 0;
		size           = 0;
		stream_bytes   = 0;
		ref_delta_hash = NULL;
		object_type    = (uint8_t)session->response[position] >> 4
			& 0x07;

		/* Extract the file size. */

		do {
			mask = (stream_bytes == 0 ? 0x0F : 0x7F);
			bits = (uint8_t)(session->response[position] & mask);
			size = (size << 7) + bits;
			stream_bytes++;
		}
		while (session->response[position++] & 0x80);

		/* Find the object->index referred to by the ofs-delta. */

		if (object_type == 6) {
			lookup_offset = 0;
			index_delta   = session->objects;

			do lookup_offset = (lookup_offset << 7)
				+ (session->response[position] & 0x7F) + 1;
			while (session->response[position++] & 0x80);

			while (--index_delta > 0)
				if (offset_pack - lookup_offset + 1 ==
					session->object[index_delta]->
						offset_pack)
					break;

			if (index_delta == 0)
				errc(EXIT_FAILURE, EINVAL,
					"unpack_objects: cannot find ofs-delta "
					"base object");
		}

		/* Extract the ref-delta checksum. */

		if (object_type == 7) {
			if ((ref_delta_hash = (char *)malloc(20)) == NULL)
				err(EXIT_FAILURE, "unpack_objects: malloc");

			memcpy(ref_delta_hash,
				session->response + position,
				20);

			position += 20;
		}

		/* Inflate and store the object. */

		buffer      = NULL;
		buffer_size = 0;

		z_stream stream = {
			.zalloc   = Z_NULL,
			.zfree    = Z_NULL,
			.opaque   = Z_NULL,
			.avail_in = (uint32_t)session->response_size - position,
			.next_in  = (uint8_t *)(session->response + position),
			};

		stream_code = inflateInit(&stream);

		if (stream_code == Z_DATA_ERROR)
			errc(EXIT_FAILURE, EILSEQ,
				"unpack_objects: zlib data stream failure");

		do {
			stream.avail_out = 16384,
			stream.next_out  = zlib_out;
			stream_code      = inflate(&stream, Z_NO_FLUSH);
			stream_bytes     = 16384 - stream.avail_out;

			if (stream_code == Z_DATA_ERROR)
				errc(EXIT_FAILURE, EILSEQ,
					"unpack_objects: "
					"zlib data stream failure");

			buffer = (char *)realloc(
				buffer,
				buffer_size + stream_bytes);

			if (buffer == NULL)
				err(EXIT_FAILURE, "unpack_objects: realloc");

			memcpy(buffer + buffer_size, zlib_out, stream_bytes);
			buffer_size += stream_bytes;
		}
		while (stream.avail_out == 0);

		inflateEnd(&stream);
		position += (uint32_t)stream.total_in;

		store_object(session,
			object_type,
			buffer,
			buffer_size,
			offset_pack,
			index_delta,
			ref_delta_hash);

		free(ref_delta_hash);
	}
}


/*
 * unpack_delta_integer
 *
 * Function that reconstructs a 32 bit integer from the data stream.
 */

static uint32_t
unpack_delta_integer(char *data, uint32_t *position, uint8_t bits)
{
	uint32_t result = 0, read_bytes = 0, temp = 0, mask = 8;

	/* Determine how many bytes in the stream are needed. */

	do if (bits & mask) read_bytes++;
	while (mask >>= 1);

	/*
	 * Put the bytes in their proper position based on the bit field
	 * passed in.
	 */

	if (read_bytes > 0) {
		temp = read_bytes;
		mask = 3;

		do {
			if (bits & (1 << mask))
				result += (uint32_t)(
					(uint8_t)data[*position + --temp]
					<< (mask * 8));
		}
		while (mask-- > 0);

		*position += read_bytes;
	}

	return (result);
}


/*
 * unpack_integer
 *
 * Function that reconstructs a variable length integer from the data stream.
 */

static uint32_t
unpack_integer(char *data, uint32_t *position)
{
	uint32_t result = 0, count = 0;

	do result += (uint32_t)((data[*position] & 0x7F) << (7 * count++));
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
apply_deltas(connector *session)
{
	struct object_node *delta, *base, lookup;
	int       x = 0, o = 0, delta_count = -1;
	char     *start, *merge_buffer = NULL, *layer_buffer = NULL;
	uint8_t   length_bits = 0, offset_bits = 0;
	uint32_t  deltas[BUFFER_4K], instruction = 0;
	uint32_t  offset = 0, position = 0, length = 0, layer_buffer_size = 0;
	uint32_t  new_file_size = 0, new_position = 0;
	uint64_t  merge_buffer_size = 0;

	for (o = (int)session->objects - 1; o >= 0; o--) {
		merge_buffer = NULL;
		delta        = session->object[o];
		delta_count  = 0;

		if (delta->type < 6)
			continue;

		/* Follow the chain of ofs-deltas down to the base object. */

		while (delta->type == 6) {
			deltas[delta_count++] = delta->index;
			delta = session->object[delta->index_delta];
			lookup.hash = delta->hash;
		}

		/* Find the ref-delta base object. */

		if (delta->type == 7) {
			deltas[delta_count++] = delta->index;
			lookup.hash = delta->ref_delta_hash;
			load_object(session, lookup.hash, NULL);
		}

		/* Lookup the base object and setup the merge buffer. */

		if ((base = RB_FIND(Tree_Objects, &Objects, &lookup)) == NULL)
			errc(EXIT_FAILURE, ENOENT,
				"apply_deltas: cannot find %05d -> %d/%s",
				delta->index,
				delta->index_delta,
				delta->ref_delta_hash);

		if ((merge_buffer = (char *)malloc(base->buffer_size)) == NULL)
			err(EXIT_FAILURE,
				"apply_deltas: malloc");

		load_buffer(session, base);

		memcpy(merge_buffer, base->buffer, base->buffer_size);
		merge_buffer_size = base->buffer_size;

		/* Loop though the deltas to be applied. */

		for (x = delta_count - 1; x >= 0; x--) {
			delta = session->object[deltas[x]];
			load_buffer(session, delta);

			position      = 0;
			new_position  = 0;

			/*
			 * The first unpack_integer is for the unused old file
			 * size.
			 */

			unpack_integer(delta->buffer, &position);
			new_file_size = unpack_integer(delta->buffer, &position);

			/* Make sure the layer buffer is large enough. */

			if (new_file_size > layer_buffer_size
				|| layer_buffer_size == 0) {

				layer_buffer_size = new_file_size;

				layer_buffer = (char *)realloc(
					layer_buffer,
					layer_buffer_size);

				if (layer_buffer == NULL)
					err(EXIT_FAILURE,
						"apply_deltas: realloc");
			}

			/*
			 * Loop through the copy/insert instructions and build
			 * up the layer buffer.
			 */

			while (position < delta->buffer_size) {
				instruction = (uint8_t)delta->buffer[position++];

				if (instruction & 0x80) {
					length_bits = (instruction & 0x70) >> 4;
					offset_bits = (instruction & 0x0F);

					offset = unpack_delta_integer(
						delta->buffer,
						&position,
						offset_bits);

					start = merge_buffer + offset;

					length = unpack_delta_integer(
						delta->buffer,
						&position,
						length_bits);

					if (length == 0)
						length = 65536;
				} else {
					offset    = position;
					start     = delta->buffer + offset;
					length    = instruction;
					position += length;
				}

				if (new_position + length > new_file_size)
					errc(EXIT_FAILURE, ERANGE,
						"apply_deltas: position"
						" overflow -- %u + %u > %u",
						new_position,
						length,
						new_file_size);

				memcpy(layer_buffer + new_position,
					start,
					length);

				new_position += length;
			}

			/* Make sure the merge buffer is large enough. */

			if (new_file_size > merge_buffer_size) {
				merge_buffer_size = new_file_size;

				merge_buffer = (char *)realloc(
					merge_buffer,
					merge_buffer_size);

				if (merge_buffer == NULL)
					err(EXIT_FAILURE,
						"apply_deltas: realloc");
			}

			/*
			 * Store the layer buffer in the merge buffer for the
			 * next loop iteration.
			 */

			memcpy(merge_buffer, layer_buffer, new_file_size);
			release_buffer(session, delta);
		}

		/* Store the completed object. */

		release_buffer(session, base);

		store_object(session,
			base->type,
			merge_buffer,
			new_file_size,
			0,
			0,
			NULL);
	}
}


/*
 * extract_tree_item
 *
 * Procedure that extracts mode/path/hash items in a tree and returns them in
 * a new file_node.
 */

static void
extract_tree_item(struct file_node *file, char **position)
{
	int x = 0;
	size_t path_size = 0;

	/* Extract the file mode. */

	file->mode = (mode_t)strtol(*position, (char **)NULL, 8);
	*position  = strchr(*position, ' ') + 1;

	/* Extract the file path. */

	path_size = strlen(*position) + 1;
	snprintf(file->path, path_size, "%s", *position);
	*position += path_size;

	/* Extract the file SHA checksum. */

	for (x = 0; x < 20; x++)
		snprintf(&file->hash[x * 2], 3,
			"%02x",
			(uint8_t)*(*position)++);

	file->hash[40] = '\0';
}


/*
 * save_tree
 *
 * Procedure that processes all of the obj-trees and retains the current files.
 */

static void
process_tree(connector *session, int remote_descriptor, char *hash,
             char *base_path)
{
	struct object_node  object, *found_object = NULL, *tree = NULL;
	struct file_node    file, *found_file = NULL;
	struct file_node   *new_node = NULL, *remote_file = NULL;
	struct stat         check;
	char                full_path[BUFFER_4K], *buffer = NULL;
	char                line[BUFFER_4K], *position = NULL;
	uint32_t            buffer_size = 0;
	uint32_t            new_is_dir, old_is_dir, new_is_link, old_is_link;
	mode_t              temp_mode;

	object.hash = hash;

	if ((tree = RB_FIND(Tree_Objects, &Objects, &object)) == NULL)
		errc(EXIT_FAILURE, ENOENT,
			"process_tree: tree %s -- %s cannot be found",
			base_path,
			object.hash);

	/* Remove the base path from the list of upcoming deletions. */

	load_buffer(session, tree);

	file.path  = base_path;
	found_file = RB_FIND(Tree_Local_Path, &Local_Path, &file);

	if (found_file != NULL) {
		found_file->keep = true;
		found_file->save = false;
	}

	/* Add the base path to the output. */

	if ((file.path = (char *)malloc(BUFFER_4K)) == NULL)
		err(EXIT_FAILURE, "process_tree: malloc");

	if ((file.hash = (char *)malloc(41)) == NULL)
		err(EXIT_FAILURE, "process_tree: malloc");

	snprintf(line, sizeof(line),
		"%o\t%s\t%s/\n",
		040000,
		hash,
		base_path);

	append(&buffer, &buffer_size, line, strlen(line));

	/* Process the tree items. */

	position = tree->buffer;

	while ((uint32_t)(position - tree->buffer) < tree->buffer_size) {
		extract_tree_item(&file, &position);

		snprintf(full_path, sizeof(full_path),
			"%s/%s",
			base_path,
			file.path);

		snprintf(line, sizeof(line),
			"%o\t%s\t%s\n",
			file.mode,
			file.hash,
			file.path);

		append(&buffer, &buffer_size, line, strlen(line));

		/* Recursively walk the trees and process the files/links. */

		if (S_ISDIR(file.mode)) {
			process_tree(session,
				remote_descriptor,
				file.hash,
				full_path);

			continue;
		}

		/*
		 * Locate the pack file object and local copy of
		 * the file.
		 */

		memcpy(object.hash, file.hash, 41);
		memcpy(file.path, full_path, strlen(full_path) + 1);

		found_object = RB_FIND(Tree_Objects, &Objects, &object);
		found_file   = RB_FIND(Tree_Local_Path, &Local_Path, &file);

		/* If the local file has not changed, skip it. */

		if (found_file != NULL) {
			found_file->keep = true;
			found_file->save = false;

			if (strncmp(file.hash, found_file->hash, 40) == 0)
				continue;
		}

		/* Create the submodule directory. */

		if (S_ISWHT(file.mode)) {
			make_path(full_path, 0755);

			new_node = new_file_node(
				strdup(full_path),
				file.mode,
				strdup(file.hash),
				true,
				false);

			RB_INSERT(Tree_Remote_Path, &Remote_Path, new_node);

			continue;
		}

		/*
		 * Missing objects can sometimes be found by searching
		 * the local tree.
		 */

		if (found_object == NULL) {
			load_object(session, file.hash, full_path);
			found_object = RB_FIND(Tree_Objects, &Objects, &object);
		}

		/* If the object is still missing, exit. */

		if (found_object == NULL)
			errc(EXIT_FAILURE, ENOENT,
				"process_tree: file %s -- %s cannot be found",
				full_path,
				file.hash);

		/* Otherwise retain it. */

		remote_file = RB_FIND(Tree_Remote_Path, &Remote_Path, &file);

		if (remote_file == NULL) {
			new_node = new_file_node(
				strdup(full_path),
				file.mode,
				strdup(found_object->hash),
				true,
				true);

			RB_INSERT(Tree_Remote_Path, &Remote_Path, new_node);
		} else {
			free(remote_file->hash);

			remote_file->mode = file.mode;
			remote_file->hash = strdup(found_object->hash);
			remote_file->keep = true;
			remote_file->save = true;
		}

		/* Check for permission and file type changes. */

		if (!session->clone && lstat(full_path, &check) == 0) {
			temp_mode = file.mode;

			if (temp_mode == 040000)
				temp_mode = 040755;

			if (temp_mode == 0120000)
				temp_mode = 0120755;

			if (check.st_mode != temp_mode) {
				old_is_dir  = S_ISDIR(check.st_mode);
				new_is_dir  = S_ISDIR(temp_mode);
				old_is_link = S_ISLNK(check.st_mode);
				new_is_link = S_ISLNK(temp_mode);

				if (old_is_link && !new_is_link) {
					unlink(full_path);
				} else if (!old_is_dir && new_is_dir) {
					unlink(full_path);

					if (session->verbosity
						&& session->display_depth > 0)
						printf(" - %s\n", full_path);
				} else if (old_is_dir && !new_is_dir) {
					prune_tree(session, full_path);

					if (session->verbosity
						&& session->display_depth > 0)
						printf(" - %s\n", full_path);
				} else {
					chmod(full_path, temp_mode);

					if (session->verbosity
						&& session->display_depth > 0)
						printf(" * %s (%o -> %o)\n",
							full_path,
							check.st_mode,
							temp_mode);
				}
			}
		}
	}

	/* Add the tree data to the remote data list. */

	release_buffer(session, tree);
	write(remote_descriptor, buffer, buffer_size);
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
save_repairs(connector *session)
{
	struct object_node  find_object, *found_object;
	struct file_node   *local_file, *remote_file, *found_file;
	struct stat         st;
	char               *check_hash = NULL, *buffer_hash = NULL;
	bool                missing = false, update = false;

	/*
	 * Loop through the remote file list, looking for objects that arrived
	 * in the pack data.
	 */

	RB_FOREACH(found_file, Tree_Remote_Path, &Remote_Path) {
		find_object.hash = found_file->hash;

		found_object = RB_FIND(Tree_Objects, &Objects, &find_object);

		if (found_object == NULL)
			continue;

		/* Save the object. */

		if (S_ISDIR(found_file->mode)) {
			if (mkdir(found_file->path, 0755) == -1
				&& errno != EEXIST)

				err(EXIT_FAILURE,
					"save_repairs: cannot create %s",
					found_file->path);
		} else {
			missing = stat(found_file->path, &st) != 0;
			update  = true;

			/*
			 * Because identical files can exist in multiple places,
			 * only update the altered files.
			 */

			if (missing == false) {
				load_buffer(session, found_object);

				check_hash = calculate_file_hash(
					found_file->path,
					st.st_mode);

				buffer_hash = calculate_object_hash(
					found_object->buffer,
					found_object->buffer_size,
					3);

				release_buffer(session, found_object);

				if (strncmp(check_hash, buffer_hash, 40) == 0)
					update = false;
			}

			if (update == true) {
				load_buffer(session, found_object);

				save_file(found_file->path,
					found_file->mode,
					found_object->buffer,
					found_object->buffer_size,
					session->verbosity,
					session->display_depth);

				release_buffer(session, found_object);

				if (strstr(found_file->path, "UPDATING"))
					extend_updating_list(session,
						found_file->path);
			}
		}
	}

	/* Make sure no files are deleted. */

	RB_FOREACH(remote_file, Tree_Remote_Path, &Remote_Path) {
		local_file = RB_FIND(Tree_Local_Path, &Local_Path, remote_file);

		if (local_file != NULL)
			local_file->keep = true;
	}
}


/*
 * save_commit_history
 *
 * Procedure that saves the commit history to disk.
 */

static void
save_commit_history(connector *session)
{
	struct object_node *found_object = NULL;
	char path[BUFFER_4K];
	int  fd, x = 0;

	snprintf(path, BUFFER_4K, "%s.new", session->remote_history_file);

	fd = open(path, O_WRONLY | O_CREAT | O_TRUNC);

	if ((fd == -1) && (errno != EEXIST))
		err(EXIT_FAILURE, "save_objects: write failure %s", path);

	RB_FOREACH(found_object, Tree_Objects, &Objects)
		if (found_object->type == 1) {
			write(fd, found_object->hash, 40);

			for (x = 0; x < found_object->parents; x++) {
				write(fd, " ", 1);
				write(fd, found_object->parent[x], 40);
			}

			write(fd, "\n", 1);
		}

	close(fd);
	chmod(path, 0644);

	if (((remove(session->remote_history_file)) != 0) && (errno != ENOENT))
		err(EXIT_FAILURE, "save_objects: cannot remove %s", path);

	if ((rename(path, session->remote_history_file)) != 0)
		err(EXIT_FAILURE, "save_objects: cannot rename %s", path);
}


/*
 * save_objects
 *
 * Procedure that commits the objects and trees to disk.
 */

static void
save_objects(connector *session)
{
	struct object_node *found_object = NULL, find_object;
	struct file_node   *found_file = NULL;
	char tree[41], path[BUFFER_4K];
	int  fd;

	/* Save the commit history. */

	save_commit_history(session);

	/* Open the remote data file. */

	snprintf(path, BUFFER_4K, "%s.new", session->remote_data_file);

	fd = open(path, O_WRONLY | O_CREAT | O_TRUNC);

	if ((fd == -1) && (errno != EEXIST))
		err(EXIT_FAILURE, "save_objects: write file failure %s", path);

	chmod(path, 0644);
	write(fd, session->want, strlen(session->want));
	write(fd, "\n", 1);

	/* Find the tree object referenced in the commit. */

	find_object.hash = session->want;
	found_object     = RB_FIND(Tree_Objects, &Objects, &find_object);

	if (found_object == NULL)
		errc(EXIT_FAILURE, EINVAL,
			"save_objects: cannot find %s",
			session->want);

	load_buffer(session, found_object);

	if (memcmp(found_object->buffer, "tree ", 5) != 0)
		errc(EXIT_FAILURE, EINVAL,
			"save_objects: first object is not a commit");

	memcpy(tree, found_object->buffer + 5, 40);
	tree[40] = '\0';

	release_buffer(session, found_object);

	/* Recursively start processing the tree. */

	process_tree(session, fd, tree, session->path_target);
	close(fd);

	/* Save the remote data list. */

	if (((remove(session->remote_data_file)) != 0) && (errno != ENOENT))
		err(EXIT_FAILURE,
			"save_objects: cannot remove %s",
			session->remote_data_file);

	if ((rename(path, session->remote_data_file)) != 0)
		err(EXIT_FAILURE,
			"save_objects: cannot rename %s",
			session->remote_data_file);

	/* Save all of the new and modified files. */

	RB_FOREACH(found_file, Tree_Remote_Path, &Remote_Path) {
		if (!found_file->save)
			continue;

		find_object.hash = found_file->hash;
		found_object = RB_FIND(Tree_Objects, &Objects, &find_object);

		if (found_object == NULL)
			errc(EXIT_FAILURE, EINVAL,
				"save_objects: cannot find %s",
				found_file->hash);

		load_buffer(session, found_object);

		save_file(found_file->path,
			found_file->mode,
			found_object->buffer,
			found_object->buffer_size,
			session->verbosity,
			session->display_depth);

		release_buffer(session, found_object);

		if (strstr(found_file->path, "UPDATING"))
			extend_updating_list(session, found_file->path);
	}
}


/*
 * extract_proxy_data
 *
 * Procedure that extracts username/password/host/port data from environment
 * variables.
 */

static void
extract_proxy_data(connector *session, const char *data)
{
	char *copy = NULL, *temp = NULL, *server = NULL, *port = NULL;
	int   offset = 0;

	if ((data) && (strstr(data, "https://") == data))
		offset = 8;

	if ((data) && (strstr(data, "http://") == data))
		offset = 7;

	if (offset == 0)
		return;

	copy = strdup(data + offset);

	/* Extract the username and password values. */

	if ((temp = strchr(copy, '@')) != NULL) {
		*temp  = '\0';
		server = temp + 1;

		if ((temp = strchr(copy, ':')) != NULL) {
			*temp = '\0';

			free(session->proxy_username);
			free(session->proxy_password);

			session->proxy_username = strdup(copy);
			session->proxy_password = strdup(temp + 1);
		}
	} else {
		server = copy;
	}

	/* If a trailing slash is present, remove it. */

	if ((temp = strchr(server, '/')) != NULL)
		*temp = '\0';

	/* Extract the host and port values. */

	if (*(server) == '[') {
		server++;

		if ((port = strchr(server, ']')) != NULL)
			*(port++) = '\0';
	} else if ((port = strchr(server, ':')) != NULL)
		*port = '\0';

	if ((server == NULL) || (port == NULL))
		errc(EXIT_FAILURE, EFAULT,
			"extract_proxy_data: malformed host/port %s", data);

	free(session->proxy_host);
	session->proxy_host = strdup(server);
	session->proxy_port = (uint16_t)strtol(port + 1, (char **)NULL, 10);

	free(copy);
}


/*
 * add_ignore
 *
 * Procedure that adds a file/directory to be list of ignored paths.
 */

static void
add_ignore(connector *session, const char *string)
{
	regex_t      reg_temp;
	int          ret_temp;
	bool         negate = (string[0] == '!' ? true : false);
	ignore_node *node = NULL;

	ret_temp = regcomp(&reg_temp,
		string + (negate ? 1 : 0),
		REG_EXTENDED | REG_NOSUB);

	if (ret_temp) {
		warnx("! warning: cannot compile %s, ignoring\n", string);
	} else {
		session->ignore = (ignore_node **)realloc(
			session->ignore,
			(session->ignores + 1) * sizeof(ignore_node *));

		if (session->ignore == NULL)
			err(EXIT_FAILURE, "add_ignore: malloc");

		if ((node = malloc(sizeof(ignore_node))) == NULL)
			err(EXIT_FAILURE, "add_ignore: malloc 2");

		if ((node->pattern = malloc(sizeof(regex_t))) == NULL)
			err(EXIT_FAILURE, "add_ignore: malloc 3");

		memcpy(node->pattern, &reg_temp, sizeof(regex_t));
		node->negate = negate;

		session->ignore[session->ignores++] = node;
	}
}


/*
 * load_config_section
 *
 * Procedure that stores the configuration options from a gitup.conf section.
 */

static void
load_config_section(connector *session, const ucl_object_t *section)
{
	const ucl_object_t *pair = NULL, *ignore = NULL;
	ucl_object_iter_t   its = NULL, iti = NULL;
	const char         *key = NULL, *string = NULL;
	char                temp[BUFFER_4K];
	long                integer;
	size_t              length = 0;
	bool                boolean, target, path, ignores;
	its = ucl_object_iterate_new(section);

	while ((pair = ucl_object_iterate_safe(its, true))) {
		key     = ucl_object_key(pair);
		string  = ucl_object_tostring(pair);
		boolean = ucl_object_toboolean(pair);

		if (ucl_object_type(pair) == UCL_INT)
			integer = ucl_object_toint(pair);
		else if (ucl_object_type(pair) == UCL_STRING)
			integer = strtol(string, (char **)NULL, 10);
		else
			integer = 0;

		if (strnstr(key, "branch", 6) != NULL) {
			free(session->branch);
			session->branch = strdup(string);
		}

		if (strnstr(key, "commit_history", 14) != NULL)
			session->commit_history = boolean;

		if (strnstr(key, "display_depth", 16) != NULL)
			session->display_depth = (uint8_t)integer;

		if (strnstr(key, "host", 4) != NULL) {
			free(session->host);
			session->host = strdup(string);

			/* Add brackets to IPv6 addresses, if needed. */

			length = strlen(session->host) + 3;

			session->host_bracketed = (char *)realloc(
				session->host_bracketed,
				length);

			if (session->host_bracketed == NULL)
				err(EXIT_FAILURE,
					"load_config_section: malloc");

			snprintf(session->host_bracketed, length,
				"%s",
				session->host);

			if (strchr(session->host, ':'))
				if (strchr(session->host, '[') == NULL)
					snprintf(session->host_bracketed,
						length,
						"[%s]",
						session->host);
		}

		if (strnstr(key, "ignores", 7) != NULL)
			ignores = true;
		else if (strnstr(key, "ignore", 6) != NULL)
			ignores = true;
		else
			ignores = false;

		if ((ignores) && (ucl_object_type(pair) == UCL_ARRAY)) {
			iti = ucl_object_iterate_new(pair);

			while ((ignore = ucl_object_iterate_safe(iti, true))) {
				string = ucl_object_tostring(ignore);
				add_ignore(session, string);
			}

			ucl_object_iterate_free(iti);
		}

		if (strnstr(key, "low_memory", 10) != NULL)
			session->low_memory = boolean;

		if (strnstr(key, "port", 4) != NULL)
			session->port = (uint16_t)integer;

		if (strnstr(key, "proxy_host", 10) != NULL) {
			free(session->proxy_host);
			session->proxy_host = strdup(string);
		}

		if (strnstr(key, "proxy_port", 10) != NULL)
			session->proxy_port = (uint16_t)integer;

		if (strnstr(key, "proxy_password", 14) != NULL) {
			free(session->proxy_password);
			session->proxy_password = strdup(string);
		}

		if (strnstr(key, "proxy_username", 14) != NULL) {
			free(session->proxy_username);
			session->proxy_username = strdup(string);
		}

		if (strnstr(key, "repository_path", 15) != NULL)
			path = true;
		else if (strnstr(key, "repository", 10) != NULL)
			path = true;
		else
			path = false;

		if (path) {
			snprintf(temp, sizeof(temp), "%s", string);

			if (temp[0] != '/')
				snprintf(temp, sizeof(temp), "/%s", string);

			free(session->repository_path);
			session->repository_path = strdup(temp);
		}

		if (strnstr(key, "source_address", 14) != NULL) {
			free(session->source_address);
			session->source_address = strdup(string);
		}

		if (strnstr(key, "target_directory", 16) != NULL)
			target = true;
		else if (strnstr(key, "target", 6) != NULL)
			target = true;
		else
			target = false;

		if (target) {
			free(session->path_target);
			session->path_target = strdup(string);

			length = strlen(session->path_target) - 1;

			if (*(session->path_target + length) == '/')
				*(session->path_target + length) = '\0';
		}

		if (strnstr(key, "verbosity", 9) != NULL)
			session->verbosity = (uint8_t)integer;

		if (strnstr(key, "work_directory", 14) != NULL) {
			free(session->path_work);
			session->path_work = strdup(string);
		}
	}

	ucl_object_iterate_free(its);
}


/*
 * load_config
 *
 * Function that loads the section options from gitup.conf
 */

static int
load_config(connector *session, const char *configuration_file, char **argv,
            int argc)
{
	struct ucl_parser  *parser = NULL;
	const ucl_object_t *section = NULL;
	ucl_object_t       *object = NULL;
	ucl_object_iter_t   it = NULL;
	const char         *target = NULL;
	char               *sections = NULL, temp[BUFFER_4K];
	uint32_t            sections_size = 0;
	uint8_t             argument_index = 0, x = 0;
	struct stat         check_file;

	/* Check to make sure the configuration file is actually a file. */

	stat(configuration_file, &check_file);

	if (!S_ISREG(check_file.st_mode))
		errc(EXIT_FAILURE, EFTYPE,
			"load_config: cannot load %s",
			configuration_file);

	/* Load and process the configuration file. */

	parser = ucl_parser_new(0);

	if (ucl_parser_add_file(parser, configuration_file) == false) {
		fprintf(stderr,
			"load_config: %s\n",
			ucl_parser_get_error(parser));

		exit(EXIT_FAILURE);
	}

	object = ucl_parser_get_object(parser);
	it     = ucl_object_iterate_new(object);

	while ((section = ucl_object_iterate_safe(it, true))) {
		target = ucl_object_key(section);

		if (strncmp(target, "defaults", 8) == 0) {
			load_config_section(session, section);
		} else {
			/*
			* Add the section to the list of known sections in case
			* a valid section is not found.
			*/

			snprintf(temp, sizeof(temp), "\t* %s\n", target);
			append(&sections, &sections_size, temp, strlen(temp));
		}

		/* Look for the section in the command line arguments. */

		if (argument_index)
			continue;

		for (x = 0; x < argc; x++)
			if (strncmp(argv[x], target, strlen(target)) == 0)
				if (strlen(argv[x]) == strlen(target)) {
					argument_index = x;

					if (session->section)
						free(session->section);

					session->section = strdup(argv[x]);
					load_config_section(session, section);
				}
	}

	ucl_object_iterate_free(it);
	ucl_object_unref(object);
	ucl_parser_free(parser);

	/*
	 * Check to make sure all of the required information was found in the
	 * configuration file.
	 */

	if (argument_index == 0)
		errc(EXIT_FAILURE, EINVAL,
			"\nCannot find a matching section in the command line "
			"arguments.  These are the configured sections:\n%s",
			sections);

	if (session->branch == NULL)
		errc(EXIT_FAILURE, EINVAL,
			"No branch found in [%s]",
			session->section);

	if (session->host == NULL)
		errc(EXIT_FAILURE, EDESTADDRREQ,
			"No host found in [%s]",
			session->section);

	if (session->path_target == NULL)
		errc(EXIT_FAILURE, EINVAL,
			"No target path found in [%s]",
			session->section);

	if (session->path_work == NULL)
		errc(EXIT_FAILURE, EINVAL,
			"No work directory found in [%s]",
			session->section);

	if (session->port == 0)
		errc(EXIT_FAILURE, EDESTADDRREQ,
			"No port found in [%s]",
			session->section);

	if (session->repository_path == NULL)
		errc(EXIT_FAILURE, EINVAL,
			"No repository found in [%s]",
			session->section);

	/* Extract username/password/host/port from the environment. */

	extract_proxy_data(session, getenv("HTTP_PROXY"));
	extract_proxy_data(session, getenv("HTTPS_PROXY"));

	free(sections);

	load_gitignore(session);

	return (argument_index);
}


/*
 * load_gitignore
 *
 * Function that loads the repository's .gitignore file, converts the
 * entries to regular expressions and adds them to the ignores list.
 */

static void
load_gitignore(connector *session)
{
	struct stat  file;
	char         path[BUFFER_4K], *buffer = NULL;
	char         source[BUFFER_4K], target[BUFFER_4K];
	char        *line_start = NULL, *line_end = NULL, *trim = NULL;
	char        *cursor = NULL, c;
	bool         in_bracket = false, separator_exists = false;
	bool         directory_only = false;
	uint32_t     buffer_size = 0, source_offset = 0, target_offset = 0;
	size_t       source_length = 0;

	snprintf(path, BUFFER_4K, "%s/.gitignore", session->path_target);

	if (stat(path, &file) == -1)
		return;

	load_file(path, &buffer, &buffer_size);

	line_start = buffer;

	while (line_start < buffer + buffer_size) {
		line_end         = strchr(line_start, '\n');
		*line_end        = '\0';
		trim             = line_end - 1;
		cursor           = line_start;
		source_offset    = 0;
		target_offset    = 0;
		directory_only   = false;
		in_bracket       = false;
		separator_exists = false;

		bzero(source, BUFFER_4K);
		bzero(target, BUFFER_4K);

		/* Skip comments and blank lines. */

		if ((*line_start == '#') || (line_start == line_end)) {
			line_start = line_end + 1;
			continue;
		}

		/* Adjust negated patterns. */

		if (*line_start == '!') {
			target[target_offset++] = '!';
			line_start++;
		}

		/*
		 * Remove unescaped trailing spaces and check if the pattern
		 * should only apply to directories.
		 */

		while ((trim > line_start)
			&& (*trim == ' ')
			&& (*(trim - 1) != '\\'))
				*trim-- = '\0';

		if (*trim == '/')
			directory_only = true;

		/*
		 * Scan the line for separators (ignoring the last character)
		 * and prepend the target path if one is found.
		 */

		source_length = strlen(line_start);

		if (source_length + 1 > BUFFER_4K)
			errc(EXIT_FAILURE, EOVERFLOW,
				"load_gitignore: "
				"Malformed .gitignore line \"%s\"",
				line_start);

		while (cursor < line_end - 1)
			if (*cursor++ == '/') {
				snprintf(source, BUFFER_4K,
					"%s/%s",
					session->path_target,
					line_start
						+ (*line_start == '/' ? 1 : 0));

				source_length    = strlen(source);
				separator_exists = true;
				break;
			}

		if (!separator_exists)
			snprintf(source, BUFFER_4K, "%s", line_start);

		/* Prepend a '/' for entries that are just filenames. */

		if (!separator_exists)
			target[target_offset++] = '/';

		/* Convert each line into a regular expression pattern. */

		while (source_offset < source_length) {
			c = source[source_offset++];

			if (c == '\r') {
				continue;
			} else if (c == '?') {
				snprintf(target + target_offset, 5, "[^/]");
				target_offset += 4;
			} else if (c == '[') {
				in_bracket = true;
				target[target_offset++] = c;
			} else if (c == ']') {
				in_bracket = false;
				target[target_offset++] = c;
			} else if (c == '.') {
				target[target_offset++] = '\\';
				target[target_offset++] = c;
			} else if ((c == '-') && (!in_bracket)) {
				target[target_offset++] = '\\';
				target[target_offset++] = c;
			} else if (c == '*' && source[source_offset] == '*') {
				snprintf(target + target_offset, 3, ".*");
				source_offset += 1;
				target_offset += 2;
			} else if (c == '*') {
				snprintf(target + target_offset, 6, "[^/]+");
				target_offset += 5;
			} else {
				target[target_offset++] = c;
			}

			if (target_offset > BUFFER_4K - 8)
				errc(EXIT_FAILURE, EOVERFLOW,
					"load_gitignore: "
					"Malformed .gitignore line \"%s\"",
					source);
		}

		/* Complete and retain the pattern(s). */

		if (directory_only) {
			snprintf(target + target_offset, 4, ".*$");
			add_ignore(session, target);
		} else {
			snprintf(target + target_offset, 5, "/.*$");
			add_ignore(session, target);

			snprintf(target + target_offset, 2, "$");
			add_ignore(session, target);
		}

		if (session->verbosity > 2)
			fprintf(stderr, "# .gitignore: %-51s ==> %s\n",
				source,
				target);

		line_start = line_end + 1;
	}

	free(buffer);
}

/*
 * extract_command_line_want
 *
 * Procedure that stores the pack data file from the command line argument,
 * extracts the want and creates the pack commit data file name.
 */

static void
extract_command_line_want(connector *session, char *option)
{
	char   *extension = NULL, *temp = NULL, *want = NULL, *start = NULL;
	size_t  length = 0;

	if (!path_exists(option))
		err(EXIT_FAILURE,
			"extract_command_line_want: %s",
			option);

	session->use_pack_file  = true;
	session->pack_data_file = strdup(option);

	length    = strlen(option);
	start     = option;
	extension = strnstr(option, ".pack", length);

	/* Build the pack commit history file name. */

	session->pack_history_file = (char *)malloc(length + 10);

	if (session->pack_history_file == NULL)
		err(EXIT_FAILURE, "extract_command_line_want: malloc");

	snprintf(session->pack_history_file, length + 9,
		"%s.history",
		option);

	/* Try and extract the want from the file name. */

	while ((temp = strchr(start, '/')) != NULL)
		start = temp + 1;

	length -= (size_t)(start - option);
	want    = strnstr(start, session->section, length);

	if (want == NULL)
		return;
	else
		want += strlen(session->section) + 1;

	if (extension != NULL)
		*extension = '\0';

	if (strlen(want) == 40)
		session->want = strdup(want);
}


/*
 * usage
 *
 * Procedure that prints a summary of command line options and exits.
 */

static void
usage(const char *configuration_file)
{
	fprintf(stderr,
		"Usage: gitup <section> [-cklrV] [-h checksum] [-t tag] "
		"[-u pack file] [-v verbosity] [-w checksum]\n"
		"  Please see %s for the list of <section> options.\n\n"
		"  Options:\n"
		"    -C  Override the default configuration file.\n"
		"    -c  Force gitup to clone the repository.\n"
		"    -d  Limit the display of changes to the specified number "
		"of\n"
		"          directory levels deep (0 = display the entire path)."
		"\n"
		"    -h  Override the 'have' checksum.\n"
		"    -k  Save a copy of the pack data to the current working "
		"directory.\n"
		"    -l  Low memory mode -- stores temporary object data to "
		"disk.\n"
		"    -r  Repair all missing/modified files in the local "
		"repository.\n"
		"    -t  Fetch the commit referenced by the specified tag.\n"
		"    -u  Path to load a copy of the pack data, skipping the "
		"download.\n"
		"    -v  How verbose the output should be (0 = no output, 1 = "
		"the default\n"
		"          normal output, 2 = also show debugging information)."
		"\n"
		"    -V  Display gitup's version number and exit.\n"
		"    -w  Override the 'want' checksum.\n"
		"\n", configuration_file);

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
	struct file_node   *file   = NULL, *next_file   = NULL;

	char     *command = NULL, *display_path = NULL, *temp = NULL, hash[20];
	char     *configuration_file = NULL, *remote_data_file_hash = NULL;
	char      base64_credentials[BUFFER_4K];
	char      credentials[BUFFER_4K];
	char      section[BUFFER_4K];
	char      gitup_revision[BUFFER_4K];
	char      gitup_revision_path[BUFFER_4K];
	char      cache_path[BUFFER_4K], git_check[BUFFER_4K];
	int       option = 0;
	size_t    length = 0;
	int       x = 0, base64_credentials_length = 0, skip_optind = 0;
	uint32_t  o = 0, local_file_count = 0;
	uint8_t   save_verbosity = 0;
	bool      encoded = false, just_added = false;
	bool      current_repository = false, path_target_exists = false;
	bool      remote_data_exists = false, remote_history_exists = false;
	bool      pack_data_exists = false;
	bool      pruned = false;
	DIR      *directory = NULL;

#if OPENSSL_VERSION_NUMBER < 0x10100000L
	EVP_ENCODE_CTX      evp_ctx;
#else
	EVP_ENCODE_CTX     *evp_ctx;
#endif

	connector session = {
		.ssl                 = NULL,
		.ctx                 = NULL,
		.socket_descriptor   = 0,
		.source_address      = NULL,
		.host                = NULL,
		.host_bracketed      = NULL,
		.port                = 0,
		.proxy_host          = NULL,
		.proxy_port          = 0,
		.proxy_username      = NULL,
		.proxy_password      = NULL,
		.proxy_credentials   = NULL,
		.section             = NULL,
		.repository_path     = NULL,
		.branch              = NULL,
		.tag                 = NULL,
		.have                = NULL,
		.want                = NULL,
		.response            = NULL,
		.response_blocks     = 0,
		.response_size       = 0,
		.clone               = false,
		.repair              = false,
		.object              = NULL,
		.objects             = 0,
		.pack_data_file      = NULL,
		.pack_history_file   = NULL,
		.path_target         = NULL,
		.path_target_custom  = false,
		.path_work           = NULL,
		.remote_data_file    = NULL,
		.remote_history_file = NULL,
		.ignore              = NULL,
		.ignores             = 0,
		.commit_history      = false,
		.keep_pack_file      = false,
		.use_pack_file       = false,
		.verbosity           = 1,
		.display_depth       = 0,
		.updating            = NULL,
		.low_memory          = false,
		.cache               = -1,
		.cache_length        = 0,
		};

	configuration_file = strdup(CONFIG_FILE_PATH);

	if (argc < 2)
		usage(configuration_file);

	for (x = 0; x < argc; x++)
		if (strlen(argv[x]) == 2)
			if (strncmp(argv[x], "-V", 2) == 0) {
				printf("gitup version %s\n", GITUP_VERSION);
				exit(EXIT_SUCCESS);
			}

	/* Check to see if the configuration file path is being overridden. */

	for (x = 0; x < argc; x++)
		if (strnstr(argv[x], "-C", 2) == argv[x]) {
			if (strlen(argv[x]) > 2) {
				if (configuration_file)
					free(configuration_file);

				configuration_file = strdup(argv[x] + 2);
			} else if ((argc > x) && (argv[x + 1][0] != '-')) {
				if (configuration_file)
					free(configuration_file);

				configuration_file = strdup(argv[x + 1]);
			}
		}

	/*
	 * Load the configuration file to learn what section is being requested.
	 */

	skip_optind = load_config(&session, configuration_file, argv, argc);

	if (skip_optind == 1)
		optind++;

	/* Process the command line parameters. */

	while ((option = getopt(argc, argv,
		"C:cd:h:I:klrp:S:t:u:v:w:")) != -1) {
		switch (option) {
			case 'C':
				if (session.verbosity)
					fprintf(stderr,
						"# Configuration file: %s\n",
						configuration_file);
				break;
			case 'c':
				session.clone = true;
				break;
			case 'd':
				session.display_depth = (uint8_t)strtol(
					optarg,
					(char **)NULL,
					10);
				break;
			case 'h':
				session.have = strdup(optarg);
				break;
			case 'I':
				add_ignore(&session, optarg);
				break;
			case 'k':
				session.keep_pack_file = true;
				break;
			case 'l':
				session.low_memory = true;
				break;
			case 'p':
				session.path_target_custom = true;
				free(session.path_target);
				session.path_target = absolute_path(optarg);
				break;
			case 'r':
				session.repair = true;
				break;
			case 'S':
				session.source_address = strdup(optarg);
				break;
			case 't':
				session.tag = strdup(optarg);
				break;
			case 'u':
				extract_command_line_want(&session, optarg);
				break;
			case 'v':
				session.verbosity = (uint8_t)strtol(
					optarg,
					(char **)NULL,
					10);
				break;
			case 'w':
				session.want = strdup(optarg);
				break;
		}

		if (optind == skip_optind)
			optind++;
	}

	/* Warn if the configuration file is old. */

	if (strstr(session.repository_path, ".git") == NULL)
		fprintf(stderr,
			"! The [%s] section in %s uses an outdated repository "
			"path.\n! Please consider upgrading it with the latest "
			"version at\n! https://github.com/johnmehr/gitup/"
			"blob/main/gitup.conf\n",
			session.section,
			configuration_file);

	/* Build the proxy credentials string. */

	if (session.proxy_username) {
		snprintf(credentials, sizeof(credentials),
			"%s:%s",
			session.proxy_username,
			session.proxy_password);

#if OPENSSL_VERSION_NUMBER < 0x10100000L
		EVP_EncodeInit(&evp_ctx);

		EVP_EncodeUpdate(&evp_ctx,
			(unsigned char *)base64_credentials,
			&base64_credentials_length,
			(unsigned char *)credentials,
			(int)strlen(credentials));

		EVP_EncodeFinal(&evp_ctx,
			(unsigned char *)base64_credentials,
			&base64_credentials_length);
#else
		evp_ctx = EVP_ENCODE_CTX_new();

		EVP_EncodeInit(evp_ctx);

		EVP_EncodeUpdate(evp_ctx,
			(unsigned char *)base64_credentials,
			&base64_credentials_length,
			(unsigned char *)credentials,
			(int)strlen(credentials));

		EVP_EncodeFinal(evp_ctx,
			(unsigned char *)base64_credentials,
			&base64_credentials_length);

		EVP_ENCODE_CTX_free(evp_ctx);
#endif

		/* Remove the trailing return. */

		if ((temp = strchr(base64_credentials, '\n')) != NULL)
			*temp = '\0';

		length = 30 + strlen(base64_credentials);

		session.proxy_credentials = (char *)malloc(length + 1);

		if (session.proxy_credentials == NULL)
			err(EXIT_FAILURE, "main: malloc");

		snprintf(session.proxy_credentials, length,
			"Proxy-Authorization: Basic %s\r\n",
			base64_credentials);
	} else {
		session.proxy_credentials = (char *)malloc(1);

		if (session.proxy_credentials == NULL)
			err(EXIT_FAILURE, "main: malloc");

		session.proxy_credentials[0] = '\0';
	}

	/* If a tag and a want are specified, warn and exit. */

	if (session.tag && session.want)
		errc(EXIT_FAILURE, EINVAL,
			"A tag and a want cannot both be requested");

	/* Create the work path and build the remote data and history paths. */

	make_path(session.path_work, 0755);

	length = strlen(session.path_work) + strlen(session.section) + 22;

	session.remote_data_file = (char *)malloc(length + 1);

	if (session.remote_data_file == NULL)
		err(EXIT_FAILURE, "main: malloc");

	SHA1((uint8_t *)session.path_target,
		strlen(session.path_target),
		(uint8_t *)hash);

	remote_data_file_hash = legible_hash(hash);

	snprintf(session.remote_data_file, length + 1,
		"%s/%s%s%s",
		session.path_work,
		session.section,
		(session.path_target_custom ? "-" : ""),
		(session.path_target_custom ? remote_data_file_hash : ""));

	free(remote_data_file_hash);

	session.remote_history_file = (char *)malloc(length + 9);

	if (session.remote_history_file == NULL)
		err(EXIT_FAILURE, "main: malloc");

	snprintf(session.remote_history_file, length + 9,
		"%s/%s.history",
		session.path_work,
		session.section);

	/* If non-alphanumerics exist in the section, encode them. */

	temp   = strdup(session.remote_data_file);
	length = strlen(session.section);

	for (o = 0; o < length - 1; o++) {
		uint8_t c = (uint8_t)session.section[o];

		if (!isalpha(c) && !isdigit(c)) {
			session.section = (char *)realloc(
				session.section,
				length + 2);

			if (session.section == NULL)
				err(EXIT_FAILURE, "main: realloc");

			memcpy(section, session.section + o + 1, length - o);
			snprintf(session.section + o, length - o + 3,
				"%%%X%s",
				session.section[o],
				section);

			length += 2;
			o += 2;
			encoded = true;
		}
	}

	if (encoded == true) {
		/* Store the updated remote data path. */

		length += strlen(session.path_work) + 1;

		session.remote_data_file = (char *)realloc(
			session.remote_data_file,
			length + 1);

		if (session.remote_data_file == NULL)
			err(EXIT_FAILURE, "main: realloc");

		snprintf(session.remote_data_file, length + 1,
			"%s/%s",
			session.path_work,
			session.section);

		/* If a non-encoded remote data path exists, rename it. */

		if (path_exists(temp))
			if (rename(temp, session.remote_data_file) != 0)
				err(EXIT_FAILURE,
					"main: cannot rename %s",
					session.remote_data_file);
	}

	free(temp);

	/*
	 * If the remote files list or repository are missing, then a clone
	 * must be performed.
	 */

	path_target_exists    = path_exists(session.path_target);
	pack_data_exists      = path_exists(session.pack_data_file);
/*	pack_history_exists   = path_exists(session.pack_history_file); */
	remote_data_exists    = path_exists(session.remote_data_file);
	remote_history_exists = path_exists(session.remote_history_file);

	/* Setup the temporary object cache file. */

	if (session.low_memory) {
		snprintf(cache_path, BUFFER_4K,
			"%s.cache",
			session.remote_data_file);

		session.cache = open(cache_path, O_RDWR | O_CREAT | O_TRUNC);

		if (session.cache == -1)
			err(EXIT_FAILURE,
				"unpack_objects: object file write failure %s",
				cache_path);

		chmod(cache_path, 0644);
		unlink(cache_path);
	}

	/*
	 * If path_target exists and is empty, do not load local data and
	 * perform a clone.
	 */

	if ((directory = opendir(session.path_target)) != NULL) {
		while (readdir(directory) != NULL)
			local_file_count++;

		closedir(directory);
	}

	if (local_file_count <= 2)
		path_target_exists = false;

	/* If path_target and remote_data exist, load the known repo data. */

	if (path_target_exists) {
		snprintf(git_check, BUFFER_4K, "%s/.git", session.path_target);

		if (path_exists(git_check))
			errc(EXIT_FAILURE, EEXIST,
				"A .git directory was found -- gitup does not "
				"update this directory which will cause "
				"problems for the official Git client.  If you "
				"wish to use gitup, please remove %s and "
				"rerun gitup.",
				git_check);

		if (remote_data_exists)
			load_remote_data(&session);

		if (session.clone) {
			if (path_target_exists)
				errc(EXIT_FAILURE, EEXIST,
					"The target directory %s contains "
					"files. Cloning over an existing "
					"repository will leave old files "
					"behind, potentially causing problems. "
					"Please remove the contents of %s and "
					"rerun gitup.",
					session.path_target,
					session.path_target);
		} else {
			if (session.verbosity)
				fprintf(stderr,
					"# Scanning local repository...\n");

			scan_local_repository(&session, session.path_target);
		}
	} else {
		session.clone = true;
	}

	/* Display session parameters. */

	if (session.verbosity) {
		fprintf(stderr, "# Host: %s\n", session.host);
		fprintf(stderr, "# Port: %d\n", session.port);

		if (session.source_address)
			fprintf(stderr,
				"# Source Address: %s\n",
				session.source_address);

		if (session.proxy_host)
			fprintf(stderr,
				"# Proxy Host: %s\n"
				"# Proxy Port: %d\n",
				session.proxy_host,
				session.proxy_port);

		if (session.proxy_username)
			fprintf(stderr,
				"# Proxy Username: %s\n",
				session.proxy_username);

		fprintf(stderr,
			"# Repository Path: %s\n"
			"# Target Directory: %s\n",
			session.repository_path,
			session.path_target);
/*
		fprintf(stderr,
			"# Commit History: %s\n",
			(session.commit_history ? "yes" : "no"));
*/
		if (session.use_pack_file == true)
			fprintf(stderr,
				"# Using pack file: %s\n",
				session.pack_data_file);

		if (session.tag)
			fprintf(stderr, "# Tag: %s\n", session.tag);

		if (session.have)
			fprintf(stderr, "# Have: %s\n", session.have);

		if (session.want)
			fprintf(stderr, "# Want: %s\n", session.want);

		if (session.low_memory)
			fprintf(stderr, "# Low memory mode: Yes\n");
	}

	/* Adjust the display depth to include path_target. */

	if (session.display_depth > 0) {
		temp = session.path_target;

		while ((temp = strchr(temp + 1, '/')))
			session.display_depth++;
	}

	/* Setup the session to the server. */

	connect_server(&session);

	if (session.proxy_host)
		create_tunnel(&session);

	setup_ssl(&session);

	/* Execute the fetch, unpack, apply deltas and save. */

	if (!session.use_pack_file
		|| (session.use_pack_file && !pack_data_exists))
		get_commit_details(&session);

	if (session.have && session.want
		&& (strncmp(session.have, session.want, 40) == 0))
		current_repository = true;

	/* Fetch the commit history. */

	if (session.commit_history) {
		load_pack(&session, session.pack_history_file, true);

		if (!remote_history_exists)
			save_commit_history(&session);
	}

	/* When pulling, first ensure the local tree is pristine. */

	if (session.repair || !session.clone) {
		command = build_repair_command(&session);

		if (command == NULL) {
			session.repair = false;
		} else {
			session.repair = true;

			if (session.verbosity)
				fprintf(stderr, "# Action: repair\n");

			fetch_pack(&session, command);
			apply_deltas(&session);
			save_repairs(&session);
		}
	}

	/* Process the clone or pull. */

	if (!current_repository && !session.repair) {
		load_pack(&session, session.pack_data_file, false);

		if (session.verbosity)
			fprintf(stderr,
				"# Action: %s\n",
				(session.clone ? "clone" : "pull"));

		apply_deltas(&session);
		save_objects(&session);
	}

	/* Save .gituprevision. */

	if (session.want || session.tag) {
		snprintf(gitup_revision_path, BUFFER_4K,
			"%s/.gituprevision",
			session.path_target);

		snprintf(gitup_revision, BUFFER_4K,
			"%s:%.9s\n",
			(session.tag ? session.tag : session.branch),
			session.want);

		save_file(gitup_revision_path,
			0644,
			gitup_revision,
			(uint32_t)strlen(gitup_revision),
			0,
			0);
	}

	/* Wrap it all up. */

	if (session.cache != -1)
		close(session.cache);

	RB_FOREACH_SAFE(file, Tree_Local_Hash, &Local_Hash, next_file)
		RB_REMOVE(Tree_Local_Hash, &Local_Hash, file);

	RB_FOREACH_SAFE(file, Tree_Local_Path, &Local_Path, next_file) {
		if (!file->keep && (!current_repository || session.repair)) {
			if (ignore_file(&session,
				file->path,
				IGNORE_SKIP_DELETE))
					continue;

			pruned = true;

			if (S_ISDIR(file->mode)) {
				display_path = trim_path(file->path,
					session.display_depth,
					&just_added);

				if (session.verbosity
					&& session.display_depth > 0
					&& just_added
					&& strlen(display_path)
						== strlen(file->path))
						printf(" - %s\n", display_path);

				save_verbosity = session.verbosity;
				session.verbosity = 0;
				pruned = prune_tree(&session, file->path);
				session.verbosity = save_verbosity;
				free(display_path);
			} else if (remove(file->path) && errno != ENOENT) {
				fprintf(stderr,
					" ! cannot remove %s\n",
					file->path);
			}

			if (pruned
				&& session.verbosity
				&& session.display_depth == 0)
				printf(" - %s\n", file->path);

		}

		RB_REMOVE(Tree_Local_Path, &Local_Path, file);
		file_node_free(file);
	}

	RB_FOREACH_SAFE(file, Tree_Remote_Path, &Remote_Path, next_file) {
		RB_REMOVE(Tree_Remote_Path, &Remote_Path, file);
		file_node_free(file);
	}

	RB_FOREACH_SAFE(file, Tree_Trim_Path, &Trim_Path, next_file) {
		RB_REMOVE(Tree_Trim_Path, &Trim_Path, file);
		file_node_free(file);
	}

	RB_FOREACH_SAFE(object, Tree_Objects, &Objects, next_object)
		RB_REMOVE(Tree_Objects, &Objects, object);

	for (o = 0; o < session.objects; o++) {
		if (session.verbosity > 2)
			fprintf(stdout,
				"###### %05d-%d\t%d\t%u\t%s\t%d\t%s\n",
				session.object[o]->index,
				session.object[o]->type,
				session.object[o]->offset_pack,
				session.object[o]->buffer_size,
				session.object[o]->hash,
				session.object[o]->index_delta,
				session.object[o]->ref_delta_hash);

		object_node_free(session.object[o]);
	}

	if (session.verbosity && session.updating)
		fprintf(stderr,
			"#\n# Please review the following file(s) for "
			"important changes.\n%s#\n",
			session.updating);

	for (x = 0; x < session.ignores; x++) {
		regfree(session.ignore[x]->pattern);
		free(session.ignore[x]);
	}

	free(configuration_file);
	free(session.ignore);
	free(session.response);
	free(session.object);
	free(session.source_address);
	free(session.host);
	free(session.host_bracketed);
	free(session.proxy_host);
	free(session.proxy_username);
	free(session.proxy_password);
	free(session.proxy_credentials);
	free(session.section);
	free(session.repository_path);
	free(session.branch);
	free(session.tag);
	free(session.have);
	free(session.want);
	free(session.pack_data_file);
	free(session.pack_history_file);
	free(session.path_target);
	free(session.path_work);
	free(session.remote_data_file);
	free(session.remote_history_file);
	free(session.updating);

	if (session.ssl) {
		SSL_shutdown(session.ssl);
		SSL_CTX_free(session.ctx);
		close(session.socket_descriptor);
		SSL_free(session.ssl);
	}

	if (session.repair == true)
		fprintf(stderr,
			"# The local repository has been repaired.  "
			"Please rerun gitup to pull the latest commit.\n");

	if (session.verbosity)
		fprintf(stderr, "# Done.\n");

	sync();

	return (session.repair ? 2 : 0);
}
