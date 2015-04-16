#include<stdio.h>

void duffs_device(unsigned char *from, unsigned char *to, int count) {
  int n = (count + 7) / 8;
  switch(count % 8) {
    case 0: do { *to++ = *from++;
    case 7: *to++ = *from++;
    case 6: *to++ = *from++;
    case 5: *to++ = *from++;
    case 4: *to++ = *from++;
    case 3: *to++ = *from++;
    case 2: *to++ = *from++;
    case 1: *to++ = *from++;
               } while(--n > 0);
  }
}

int main() {
  long long a[10], b[10];
  for (int i = 0; i < 10; i++) a[i] = i;
  duffs_device((unsigned char*)a, (unsigned char*)b, sizeof(a));
  for (int i = 0; i < 10; i++) printf("%d\n", b[i]);
}
