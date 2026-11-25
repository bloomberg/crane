#include <local_fix_alias_acc_join.h>
#include <iostream>
int main() {
  std::cout << LocalFixAliasAccJoin::result << std::endl;
  return LocalFixAliasAccJoin::result == 7 ? 0 : 1;
}
