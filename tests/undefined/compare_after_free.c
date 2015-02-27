#include<stdlib.h>
#include<stdio.h>

int main() {
  int *p = malloc(sizeof(int));
  free(p);
  int *q = malloc(sizeof(int));
  printf("%d\n", p == q);
  return 0;
}
