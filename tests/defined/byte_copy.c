
int main() {
  struct { short x, *r; } s1, s2;
  s1.x = 10;
  s1.r = &s1.x;
  for (int i = 0; i < sizeof(s1); i++)
    ((unsigned char*)&s2)[i] = ((unsigned char*)&s1)[i];
  return *s2.r;
}

