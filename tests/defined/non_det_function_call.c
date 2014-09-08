int x = 0;
int f(int y) { return (x = y); }
int main() { f(3) + f(4); return x; }

