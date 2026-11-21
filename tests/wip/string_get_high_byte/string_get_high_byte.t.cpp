#include <string_get_high_byte.h>

#include <iostream>

int main() {
  auto code = StringGetHighByte::first_code;
  bool above = StringGetHighByte::high_above_low;
  std::cout << code << " " << above << std::endl;
  return (code == 195 && above) ? 0 : 1;
}
