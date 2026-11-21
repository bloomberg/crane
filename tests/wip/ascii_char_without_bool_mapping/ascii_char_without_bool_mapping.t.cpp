#include <ascii_char_without_bool_mapping.h>

#include <iostream>

int main() {
  // bool is not mapped here: it is the generated enum, whose first
  // enumerator is true.
  int v = static_cast<int>(AsciiCharWithoutBoolMapping::code_is_66);
  std::cout << (v == 0 ? "true" : "false") << std::endl;
  return v == 0 ? 0 : 1;
}
