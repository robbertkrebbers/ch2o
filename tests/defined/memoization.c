#include<stdio.h>

int expensive_function(int y) {
  printf("very expensive identity\n");
  return y;
}

int f(int y) {
  static int map[10];
  if (map[y]) { return map[y]; }
  return map[y] = expensive_function(y);
}

int main() {
  return f(2) + f(2);
}
