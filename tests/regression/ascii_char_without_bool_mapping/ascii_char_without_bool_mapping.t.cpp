#include <ascii_char_without_bool_mapping.h>

#include <iostream>

int main() {
  // Mapping.AsciiChar exports Mapping.Shared: bool is C++ bool.
  bool v = AsciiCharWithoutBoolMapping::code_is_66;
  std::cout << (v ? "true" : "false") << std::endl;
  return v ? 0 : 1;
}
