#include <loopify_partner_self_in_closure.h>
#include <iostream>
int main() {
  bool ok = LoopifyPartnerSelfInClosure::check(std::monostate{});
  std::cout << (ok ? "ok" : "wrong") << std::endl;
  return ok ? 0 : 1;
}
