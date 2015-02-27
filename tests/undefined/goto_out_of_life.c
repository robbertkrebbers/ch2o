#include<stddef.h>

int main() {
  int *p = NULL;
  l:
  if (p) { return (*p); }
  else { int j = 10; p = &j; goto l; }
}

