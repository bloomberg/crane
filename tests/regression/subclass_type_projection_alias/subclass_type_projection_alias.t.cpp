#include <cassert>
#include <subclass_type_projection_alias.h>

// Follows Tau to the Ret of a tree over no events.
template <typename Tree> static auto run_itree(Tree t) {
  for (;;) {
    auto o = t.observe();
    using Obs = decltype(o);
    if (auto *r = std::get_if<typename Obs::RetF>(&o.v()))
      return r->r;
    auto *s = std::get_if<typename Obs::TauF>(&o.v());
    assert(s);
    Tree next = s->t;
    t = std::move(next);
  }
}

int main() {
  using D = SubclassTypeProjectionAlias::dv<Nat>;
  const auto r = run_itree(SubclassTypeProjectionAlias::run());
  assert((std::holds_alternative<typename Sum<SubclassTypeProjectionAlias::Err,
                                              D>::Inr>(r.v())));
  const auto &[d] =
      std::get<typename Sum<SubclassTypeProjectionAlias::Err, D>::Inr>(r.v());
  assert(std::holds_alternative<typename D::DN>(d.v()));
  return 0;
}
