#include <cassert>
#include <lifted_helper_in_member_init.h>
int main() {
  assert(LiftedHelperInMemberInit::shifted.first == false);
  assert(LiftedHelperInMemberInit::doubled.first == true);
  return 0;
}
