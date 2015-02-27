#include<limits.h>
#include<stdio.h>

/* From http://www.cs.utah.edu/~regehr/papers/overflow12.pdf */
int main() {
  printf("UINT_MAX+1 = %d\n", UINT_MAX+1);
  printf("SHRT_MAX+1 = %d\n", SHRT_MAX+1);
  printf("1 << 0 = %d\n", 1 << 0);
}
