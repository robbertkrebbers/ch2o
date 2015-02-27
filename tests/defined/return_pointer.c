#include<stdio.h>

int x = 314;

int* f() { return 0; }
int** g() { return 0; }
int* h() {
  int x;
  {
    extern int x;
    return &x;
  }
}
int main() {
  printf("%d\n", *h());
}

