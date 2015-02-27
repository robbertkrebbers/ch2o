/* Dummy types, these will be overwritten by Main.ml */
typedef unsigned long size_t;
typedef long ptrdiff_t;

#define NULL 0

/* Horrible way to encode offsetof in way that CIL parses it */
#define offsetof(t,x) __ch2o_builtin_offsetof((t)0->x)
