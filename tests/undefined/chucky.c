int x, y, *p = &y;
int f() { if (x) { p = &x; } return 0; }
int main() {
  return (x = 1) + (*p = 2) + f();
}
