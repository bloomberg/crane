#include <value_type_match_fix.h>

/// A fixpoint that captures a field from a value-type match.
///
/// BUG HYPOTHESIS: triple is a value type (stack-allocated, non-recursive).
/// When pattern matching on a value type, the fields are bound as
/// references into the stack-allocated object. If a fixpoint captures
/// these references by & and then escapes, the references dangle
/// when the function returns and the value type is destroyed.
///
/// This is different from pointer-based (shared_ptr) types where the
/// field data lives on the heap and persists as long as the shared_ptr.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
ValueTypeMatchFix::make_adder_from_triple(const ValueTypeMatchFix::triple &t) {
  const auto &[d_a0, d_a1, d_a2] =
      std::get<typename ValueTypeMatchFix::triple::MkTriple>(t.v());
  unsigned int base = ((d_a0 + d_a1) + d_a2);
  auto go_impl = [=](auto &_self_go, unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return base;
    } else {
      unsigned int x_ = x - 1;
      return (_self_go(_self_go, x_) + 1);
    }
  };
  auto go = [=](unsigned int x) mutable -> unsigned int {
    return go_impl(go_impl, x);
  };
  return std::make_optional<std::function<unsigned int(unsigned int)>>(go);
}

/// Direct capture of pattern fields (no intermediate let binding).
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
ValueTypeMatchFix::make_field_adder(const ValueTypeMatchFix::triple &t) {
  const auto &[d_a0, d_a1, d_a2] =
      std::get<typename ValueTypeMatchFix::triple::MkTriple>(t.v());
  auto go_impl = [=](auto &_self_go, unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return d_a0;
    } else {
      unsigned int x_ = x - 1;
      return (_self_go(_self_go, x_) + 1);
    }
  };
  auto go = [=](unsigned int x) mutable -> unsigned int {
    return go_impl(go_impl, x);
  };
  return std::make_optional<std::function<unsigned int(unsigned int)>>(go);
}
