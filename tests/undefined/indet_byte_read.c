#include<stdio.h>

int main() {
  struct { short x, *r; } s1;
  s1.x = 10;
  ((unsigned char*)&s1)[3] = 1;
  printf("no undef yet\n");
  s1.x = 11;
  printf("still no undef yet\n");
  printf("will never print %d\n", ((unsigned char*)&s1)[3]);
  return 10;
}
