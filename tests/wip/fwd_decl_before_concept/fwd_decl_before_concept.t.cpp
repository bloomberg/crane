#include <fwd_decl_before_concept.h>

#include <cassert>
#include <variant>

int main() {
  // fmap (= 0) (Some 0) = Some true
  auto r = FwdDeclBeforeConcept::use(std::optional<Nat>(Nat::o()));
  assert(r.has_value() && *r == true);
  return 0;
}
