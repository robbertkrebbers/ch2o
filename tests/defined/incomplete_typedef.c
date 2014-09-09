typedef struct S T;
struct S { int x; };

int main() {
  T s; s.x = 10;
  return s.x;
}
