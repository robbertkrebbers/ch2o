/* From http://www.cs.utah.edu/~regehr/papers/overflow12.pdf */
int main() {
  int x = 1 << -1;
  return 0;
}
