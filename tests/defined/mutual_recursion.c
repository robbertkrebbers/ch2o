#include<stdio.h>

int even(int);

int main() {
  for (int i = 0; i < 10; i++) printf("even %d = %d\n", i, even(i));
}

int odd(int x) {
  if (x == 0) return 0; else return even (x - 1);
}
int even(int x) {
  if (x == 0) return 1; else return odd (x - 1);
}
