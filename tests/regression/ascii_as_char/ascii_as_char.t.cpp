#include <ascii_as_char.h>

#include <cassert>
#include <iostream>
#include <type_traits>

int main() {
  static_assert(std::is_same_v<decltype(AsciiAsChar::odd_code('a')), bool>);
  assert(AsciiAsChar::odd_code('a'));
  assert(AsciiAsChar::check(std::monostate{}));
  std::cout << "All ascii_as_char tests passed!" << std::endl;
  return 0;
}
