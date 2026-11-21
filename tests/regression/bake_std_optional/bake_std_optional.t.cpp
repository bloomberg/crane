#include <bake_std_optional.h>

#include <iostream>

int main() {
  auto a = BakeStdOptional::num_value;
  auto b = BakeStdOptional::node_value;
  std::cout << a << " " << b << std::endl;
  return (a == 5 && b == 3) ? 0 : 1;
}
