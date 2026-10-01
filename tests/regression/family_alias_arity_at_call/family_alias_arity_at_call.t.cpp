#include <family_alias_arity_at_call.h>

#include <iostream>

int main() {
  auto o = FamilyAliasArityAtCall::out;
  (void)o;
  std::cout << "family_alias_arity_at_call: ok" << std::endl;
  return 0;
}
