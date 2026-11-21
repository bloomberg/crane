#include <string_literal_as_char_pointer.h>

#include <iostream>

int main() {
  auto a = StringLiteralAsCharPointer::nested;
  auto b = StringLiteralAsCharPointer::mapped;
  std::cout << a << " " << b << std::endl;
  return (a == 2 && b == 4) ? 0 : 1;
}
