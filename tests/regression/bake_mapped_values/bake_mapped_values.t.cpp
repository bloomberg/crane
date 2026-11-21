#include <bake_mapped_values.h>

#include <iostream>

int main() {
  auto a = BakeMappedValues::arr_sum;
  auto l = BakeMappedValues::label_length;
  auto d = BakeMappedValues::digits_sum;
  auto w = BakeMappedValues::word;
  auto h = BakeMappedValues::half;
  auto deep = BakeMappedValues::deep_weight;
  std::cout << a << " " << l << " " << d << " " << w << " " << h << " "
            << deep << std::endl;
  return (a == 23 && l == 8 && d == 14 && w == 42 && h == 0.5 &&
          deep == 30000)
             ? 0
             : 1;
}
