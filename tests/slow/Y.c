#include <stdlib.h>
#include <stdio.h>

typedef union word word;
union word {int _i; void *_p; word (*_f)(word, word *);};

#define return2(x, y) \
  word *c = malloc(2*sizeof(word)); \
  c[0] = x; c[1] = y; return (word){._p = c}

#define lambda_0free(f, x, t) \
  word _##f(word x, word *z) {return t;} \
  word __##f = {._f = &_##f}; \
  word f = {._p = &__##f};

#define lambda_1free(f, y, x, t) \
  word _##f(word x, word *z) {word y = *z; return t;} \
  word f(word y) {return2((word){._f = &_##f}, y);}

word apply(word f, word x) {word *c = f._p; return (*c->_f)(x, c + 1);}
word lazy_apply(word f, word x) {return2(f, x);}
word force(word e) {word *c = e._p, r = apply(c[0], c[1]); free(c); return r;}

/*
omega f := \x.f(xx)
fix := \f.(\x.f(xx))(\x.f(xx))
fact f := \x. [x ? x*f(x - 1) : 1]
fact_ := \f x. [x ? x*f(x - 1) : 1]
*/

lambda_1free(omega, f, x, apply(f, lazy_apply(x, x)))
lambda_0free(fix, f, apply(omega(f), omega(f)))
lambda_1free(fact, f, x, (word){._i =
   x._i ? x._i*apply(force(f), (word){._i = x._i - 1})._i : 1})
lambda_0free(fact_, f, fact(f))

int main() {printf("%d weeks\n",
    apply(apply(fix, fact_), (word){._i = 10})._i /60/60/24/7);}
