#include <instance_family_param.h>

#include <cassert>
#include <iostream>

int main() {
  assert(InstanceFamilyParam::is_three);
  std::cout << "instance_family_param: ok" << std::endl;
  return 0;
}
