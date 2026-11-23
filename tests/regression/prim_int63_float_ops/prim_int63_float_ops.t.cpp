#include <prim_int63_float_ops.h>

#include <iostream>

int main() {
  auto ip = PrimInt63FloatOps::int_passed;
  auto it = PrimInt63FloatOps::int_total;
  auto fp = PrimInt63FloatOps::float_passed;
  auto ft = PrimInt63FloatOps::float_total;
  std::cout << ip << "/" << it << " " << fp << "/" << ft << std::endl;
  return (ip == it && fp == ft) ? 0 : 1;
}
