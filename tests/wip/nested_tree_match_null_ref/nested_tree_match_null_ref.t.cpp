// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <nested_tree_match_null_ref.h>

#include <iostream>

int main() {
  if (NestedTreeMatchNullRef::t_5 != 100) {
    std::cout << "FAIL: t_5" << std::endl;
    return 1;
  }
  std::cout << "All nested_tree_match_null_ref tests passed!" << std::endl;
  return 0;
}
