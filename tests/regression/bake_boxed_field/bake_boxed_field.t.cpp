#include <bake_boxed_field.h>

#include <iostream>

int main() {
  auto a = BakeBoxedField::total;
  std::cout << a << std::endl;
  return a == 2 ? 0 : 1;
}
