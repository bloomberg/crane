#include <cassert>
#include <bind_continuation_binder_field_order.h>

int main() {
  const auto &r = BindContinuationBinderFieldOrder::run;
  using Elt = Dv<typename natParams::tag, typename natParams::addr>;
  assert(std::holds_alternative<typename EOU<Elt>::Ok>(r.v()));
  const auto &[dv] = std::get<typename EOU<Elt>::Ok>(r.v());
  assert(std::holds_alternative<typename Elt::DNum>(dv.v()));
  const auto &[n] = std::get<typename Elt::DNum>(dv.v());
  assert(std::holds_alternative<typename Nat::S>(n.v()));
  return 0;
}
