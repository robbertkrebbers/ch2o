#include<stdio.h>
#include<stdlib.h>

int main() {
  int x, y;
  printf("%d\n", &x == &y);
  int *p = malloc(sizeof(int)), *q = malloc(sizeof(int));
  printf("%d\n", p == q);
  struct S { int a; int b; } s, *r = &s;
  printf("%d\n", &s.a + 1 == &(r->b));
}
