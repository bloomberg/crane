#include <handler_combinator_family.h>

#include <cassert>
#include <iostream>

int main() {
  assert(HandlerCombinatorFamily::is_five);
  std::cout << "handler_combinator_family: ok" << std::endl;
  return 0;
}
