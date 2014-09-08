void my_memcpy(void *dest, void *src, int n) {
  unsigned char *p = dest, *q = src, *end = p + n;
  while (p < end) // end may be end-of-array
    *p++ = *q++;
}

int main() {
  struct S { short x; short *r; } s, s2;
  s.x = 10;
  s.r = &s.x;
  my_memcpy(&s2, &s, sizeof(struct S));
  return *(s2.r);
}

