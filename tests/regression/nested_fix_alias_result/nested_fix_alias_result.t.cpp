#include <nested_fix_alias_result.h>

#include <iostream>

int main() {
  auto a = NestedFixAliasResult::result;
  std::cout << a << std::endl;
  return a == 4 ? 0 : 1;
}
