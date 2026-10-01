#include <loopify_mutual_partial_app.h>
#include <iostream>
int main() {
  bool ok = LoopifyMutualPartialApp::check(std::monostate{});
  std::cout << (ok ? "ok" : "wrong") << std::endl;
  return ok ? 0 : 1;
}
