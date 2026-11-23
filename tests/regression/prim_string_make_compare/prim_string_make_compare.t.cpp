#include <prim_string_make_compare.h>

#include <iostream>

int main() {
  bool a = PrimStringMakeCompare::nul_length;
  bool b = PrimStringMakeCompare::cmp_lt;
  bool c = PrimStringMakeCompare::max_length_value;
  bool d = PrimStringMakeCompare::make_clamped;
  bool e = PrimStringMakeCompare::cmp_high_gt;
  bool f = PrimStringMakeCompare::cmp_prefix;
  std::cout << a << " " << b << " " << c << " " << d << " " << e << " " << f
            << std::endl;
  return (a && b && c && d && e && f) ? 0 : 1;
}
