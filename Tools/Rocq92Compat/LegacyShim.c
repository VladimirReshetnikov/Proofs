#include <errno.h>
#include <process.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <windows.h>

struct mapping {
    const char *name;
    const char *subcommand;
};

static const struct mapping mappings[] = {
    {"coqc", "c"},
    {"coqchk", "check"},
    {"coqdep", "dep"},
    {"coq_makefile", "makefile"},
    {"coqtop", "repl"},
    {"coqdoc", "doc"},
    {"coqpp", "pp-mlg"},
    {"coqnative", "native-precompile"},
    {"coqwc", "wc"},
    {"coqtex", "tex"},
};

int main(int argc, char **argv) {
    char executable[MAX_PATH];
    DWORD length = GetModuleFileNameA(NULL, executable, MAX_PATH);
    if (length == 0 || length == MAX_PATH) {
        fputs("Unable to determine the Rocq compatibility entry point.\n", stderr);
        return 2;
    }

    char *basename = strrchr(executable, '\\');
    basename = basename == NULL ? executable : basename + 1;
    char *extension = strrchr(basename, '.');
    if (extension != NULL)
        *extension = '\0';

    const char *subcommand = NULL;
    for (size_t i = 0; i < sizeof(mappings) / sizeof(mappings[0]); ++i) {
        if (_stricmp(basename, mappings[i].name) == 0) {
            subcommand = mappings[i].subcommand;
            break;
        }
    }
    if (subcommand == NULL) {
        fprintf(stderr, "Unsupported Rocq compatibility entry point: %s\n", basename);
        return 2;
    }

    char *separator = strrchr(executable, '\\');
    if (separator == NULL) {
        fputs("Rocq compatibility entry point has no directory.\n", stderr);
        return 2;
    }
    strcpy(separator + 1, "rocq.exe");

    char **child_argv = calloc((size_t)argc + 2, sizeof(char *));
    if (child_argv == NULL) {
        fputs("Unable to allocate Rocq argument vector.\n", stderr);
        return 2;
    }
    child_argv[0] = executable;
    child_argv[1] = (char *)subcommand;
    for (int i = 1; i < argc; ++i)
        child_argv[i + 1] = argv[i];

    intptr_t result = _spawnv(_P_WAIT, executable, (const char *const *)child_argv);
    free(child_argv);
    if (result == -1) {
        fprintf(stderr, "Unable to launch rocq.exe: %s\n", strerror(errno));
        return 2;
    }
    return (int)result;
}
