void inc_array(int *p, int n) {
  int *end = p + n;
  while (p < end) (*p++)++;
}

int main() {
  int a[4];
  for (int i = 0; i < 4; i++) a[i] = i;
  inc_array(a,4);
  return a[3];
}
