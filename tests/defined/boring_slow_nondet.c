#include<stdio.h>
#include<stdlib.h>

int main(void) {
  int x = 10, *p = &x;
  return *p + *p + *p + *p + *p + *p;
} 
