#include<stdio.h>

void swap(int *p, int *q) {
  int z = *p; *p = *q; *q = z;
}
int gcd(int y, int z) {
  l: if (z) {
    y = y % z; swap(&y, &z); goto l;
  }
  return y;
}

int main() {
  for (int i = 0; i < 10; i++) {
    for (int j = 0; j < 10; j++) {
      printf("gcd %d %d = %d\n", i, j, gcd(i,j));
    }
  }
  return 0;
}

