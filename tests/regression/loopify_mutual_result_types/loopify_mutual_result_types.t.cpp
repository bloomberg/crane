#include <loopify_mutual_result_types.h>
#include <iostream>
int main() {
  bool ok = LoopifyMutualResultTypes::check(std::monostate{});
  std::cout << (ok ? "ok" : "wrong") << std::endl;
  return ok ? 0 : 1;
}
