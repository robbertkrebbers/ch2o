#include<stdio.h>
#include<stdlib.h>

int main() {
  1 ? (void)printf("foo") : abort();
}
