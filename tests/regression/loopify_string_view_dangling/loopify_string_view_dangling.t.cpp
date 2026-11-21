#include <loopify_string_view_dangling.h>

#include <iostream>

int main() {
  auto a = LoopifyStringViewDangling::result;
  std::cout << a << std::endl;
  return a == 34099 ? 0 : 1;
}
