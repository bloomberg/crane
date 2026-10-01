#include <concept_after_use.h>
#include <iostream>
int main() {
  bool ok = ConceptAfterUse::check(std::monostate{});
  std::cout << (ok ? "ok" : "wrong") << std::endl;
  return ok ? 0 : 1;
}
