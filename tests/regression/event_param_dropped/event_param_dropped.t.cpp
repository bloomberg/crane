#include <event_param_dropped.h>

#include <cassert>

struct P {
  static Provenance PROV() { return Provenance::BUILD_PROVENANCE; }
};

int main() {
  // A tree that returns at once: run_exc ends in inr (inr a).
  auto t = itree_ret(crane::obj(42));
  auto r = EventParamDropped::use<P>(t);
  assert(r != nullptr);
  const auto &n = r->observe();
  using Tree = ITree<Sum<prov, prov>>;
  assert(std::holds_alternative<typename Tree::Ret>(n));
  const auto &s = std::get<typename Tree::Ret>(n).value;
  assert((std::holds_alternative<typename Sum<prov, prov>::Inr>(s.v())));
  return 0;
}
