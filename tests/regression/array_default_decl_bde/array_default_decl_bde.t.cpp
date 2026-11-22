#include <array_default_decl_bde.h>

#include <iostream>

int main() {
  auto a = ArrayDefaultDeclBde::result;
  std::cout << a << std::endl;
  return a == 5 ? 0 : 1;
}
