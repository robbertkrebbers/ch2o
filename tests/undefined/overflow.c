#include<limits.h>
#include<stdio.h>

int f(int x) { return x < x + 1; }

int main() {
  printf("INT_MAX < INT_MAX + 1 = %d\n", f(INT_MAX));
}
