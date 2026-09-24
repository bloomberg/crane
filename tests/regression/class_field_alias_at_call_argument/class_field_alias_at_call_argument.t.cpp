#include <cassert>
#include <class_field_alias_at_call_argument.h>

int main() {
  assert(std::holds_alternative<Nat::O>(
      ClassFieldAliasAtCallArgument::run.v()));
  return 0;
}
