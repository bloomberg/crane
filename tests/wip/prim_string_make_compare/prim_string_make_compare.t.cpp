#include <prim_string_make_compare.h>

#include <iostream>

int main() {
  bool a = PrimStringMakeCompare::nul_length;
  bool b = PrimStringMakeCompare::cmp_lt;
  std::cout << a << " " << b << std::endl;
  return (a && b) ? 0 : 1;
}
