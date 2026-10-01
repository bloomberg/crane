#include <instance_uses_earlier_member.h>

#include <cassert>
#include <iostream>

int main() {
  assert(InstanceUsesEarlierMember::is_one);
  std::cout << "instance_uses_earlier_member: ok" << std::endl;
  return 0;
}
