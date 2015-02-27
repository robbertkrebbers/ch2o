#include<limits.h>
#include<stdio.h>

int main() {
	int x = INT_MAX;
	x += INT_MAX + 3U;
	printf("%d\n", x);
}
