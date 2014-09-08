int g(int *p, short *q) { int x = *q; *p = 10; return x; }

int main() {
  union INT_SHO { int x; short y; } u;
  u.y = 314;
  g(&u.x, &u.y);
  return 0;
}
