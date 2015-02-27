#include<limits.h>

/* From http://www.cs.utah.edu/~regehr/papers/overflow12.pdf */
int main() {
  long x = LONG_MAX + 1;
  return 0;
}
