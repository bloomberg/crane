#include <real_mapping_get_d.h>
#include <iostream>
int main() {
  double run = static_cast<double>(RealMappingGetD::run);
  std::cout << run << std::endl;
  return run == 4.5 ? 0 : 1;
}
