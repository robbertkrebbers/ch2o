#include<stdio.h>

int main() {
  int x, y;
  if (&x + 1 == &y) printf("x and y are allocated adjacently\n");
  return 0;
}
