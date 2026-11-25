#include <local_fix_inlined_dict_destination.h>
#include <iostream>
int main() {
  std::cout << LocalFixInlinedDictDestination::result << std::endl;
  return LocalFixInlinedDictDestination::result == 4 ? 0 : 1;
}
