#include<stdio.h>

int main() {
  int x;
  int y = (x = 3) + (x = 4);
  printf("%d %d\n", x, y);
  return 0;
}

