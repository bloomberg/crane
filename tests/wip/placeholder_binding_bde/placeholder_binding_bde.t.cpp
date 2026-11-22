#include <placeholder_binding_bde.h>

#include <iostream>

int main() {
  auto a = PlaceholderBindingBde::result;
  std::cout << a << std::endl;
  return a == 7 ? 0 : 1;
}
