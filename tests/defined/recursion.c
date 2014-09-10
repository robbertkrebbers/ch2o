#include<stdio.h>

int id(int x) {
  if (x == 0) return 0; else return 1 + id(x - 1);
}

int main() {
  for (int i = 0; i < 10; i++) {
    int j = i * 30;
    printf("id %d = %d\n", j, id(j));
  }
}

