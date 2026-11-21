#include <string_get_high_byte.h>

#include <iostream>

int main() {
  auto code = StringGetHighByte::first_code;
  bool above = StringGetHighByte::high_above_low;
  auto wide = StringGetHighByte::wide_code;
  std::cout << code << " " << above << " " << wide << std::endl;
  return (code == 195 && above && wide == 295) ? 0 : 1;
}
