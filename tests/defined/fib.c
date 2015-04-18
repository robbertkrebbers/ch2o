#include <stdio.h>

int x;


int set_x(int ret_val)
{
x=1;
return ret_val;
}


int two_unspec(void)
{
x=0;
return x + set_x(1);
}


int add_zero(int val)
{
x=0;
return val - x + set_x(0);
}


int fib(int fib_num)
{
if (fib_num > 3)
    return fib(fib_num-2) + add_zero(fib(fib_num-1));
else
    if (fib_num == 3)
       return two_unspec();
    else
       return 1;
}

int main(void)
{
int n;

// scanf("%d", &n);
n=5;
printf("Fibonacci %d = %d\n", n, fib(n));
return 0;
}
