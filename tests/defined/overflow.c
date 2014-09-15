#include<limits.h>
#include<stdio.h>

int f(int x) { return x < x + 1; }

int main() {
  printf("SHRT_MAX < SHRT_MAX+1 = %d\n", f(SHRT_MAX));
}
