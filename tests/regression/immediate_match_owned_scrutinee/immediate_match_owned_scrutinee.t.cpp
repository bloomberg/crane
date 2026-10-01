#include <immediate_match_owned_scrutinee.h>
#include <iostream>
int main() {
  bool ok = ImmediateMatchOwnedScrutinee::check(std::monostate{});
  std::cout << (ok ? "ok" : "wrong") << std::endl;
  return ok ? 0 : 1;
}
