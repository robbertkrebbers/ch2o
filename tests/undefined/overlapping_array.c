#include<stdio.h>

struct A { int a [32]; };

union U {
  struct A a;
  struct { char b1; struct A b2; } b;
} u;

void init(struct A *p) {
  for (int i = 0; i < 32; i++) { p->a[i] = i; }
}

int test(struct A *p) {
  int b = 0;
  for (int i = 0; i < 32; i++) {
    printf("%d=%d\n", i, p->a[i]);
    if (p->a[i] != i) b = 1;
  }
  return b;
}

struct A g(struct A a) { return a; }

int main() {
  init(&u.a);
  u.b.b2 = u.a;
  return test(&u.b.b2);
} 
