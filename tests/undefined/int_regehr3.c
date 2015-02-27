#include<limits.h>

/* From http://www.cs.utah.edu/~regehr/papers/overflow12.pdf */
int main() {
  char c = CHAR_MAX; c++;
  return 0;
}
