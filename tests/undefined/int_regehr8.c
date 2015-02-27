#include<limits.h>

/* From http://www.cs.utah.edu/~regehr/papers/overflow12.pdf */
int main() {
  int x = INT_MIN%-1;
  return 0;
}
