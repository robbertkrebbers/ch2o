#include<stdio.h>

int x;

int main() {
  if (x != 10) printf("ERROR 1\n");
  {
    int x = 11;
    if (x != 11) printf("ERROR 2\n");
    {
      extern int x;
      if (x != 10) printf("ERROR 3\n");
    }
  }
  int *p;
  {
    static int y;
    if (y != 0) printf("ERROR 4\n");
    {
      int y = 14;
      if (y != 14) printf("ERROR 5\n");
    }
    p = &y;
    y = 16;
  }
  if (*p != 16) printf("ERROR 6\n");
  return 0;
}

int x = 10;
int x;
