#include <bake_long_list.h>

#include <iostream>

int main() {
  auto a = BakeLongList::count;
  std::cout << a << std::endl;
  return a == 30000 ? 0 : 1;
}
