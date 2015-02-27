#define malloc(size) __ch2o_builtin_malloc(size)
#define free(p) __ch2o_builtin_free(p)
#define abort() __ch2o_builtin_abort()
