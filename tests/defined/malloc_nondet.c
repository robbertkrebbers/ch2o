int main() {
  if(malloc(1)) {
    printf("foo\n");
  } else {
    printf("bar\n");
  }
}
