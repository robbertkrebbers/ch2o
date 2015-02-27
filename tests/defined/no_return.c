#include<stdio.h>

int f() {
  if(1) return 10;
}

int main() {
  printf("%d\n", f());
}
