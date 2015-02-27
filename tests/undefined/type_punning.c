#include<stdio.h>

union INT_SHO { int x; short y; };
  
int main() {
  union INT_SHO u; u.x = 311111111;
  short *p = &u.y;
  printf("%d", *p);
  return 0;
}
