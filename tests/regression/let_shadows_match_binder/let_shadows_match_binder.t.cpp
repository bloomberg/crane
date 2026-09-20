#include <let_shadows_match_binder.h>

#include <cassert>
#include <variant>

// [Nat] has no [operator==], so read the successor's payload back out.
static bool is_one(const Nat &n) {
  const auto *s = std::get_if<Nat::S>(&n.v());
  return s && std::holds_alternative<Nat::O>(s->a0->v());
}

int main() {
  // The [let] takes the branch's value, so both are one more than the payload.
  assert(is_one(LetShadowsMatchBinder::two(std::optional<Nat>(Nat::o()))));
  assert(is_one(LetShadowsMatchBinder::three(std::optional<Nat>(Nat::o()))));
  return 0;
}
