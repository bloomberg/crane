#include <loopify_result_no_default.h>
#include <iostream>
// Run an itree over no events: follow Tau, stop at Ret.
template <typename Tree> static auto run(Tree t) {
  for (;;) {
    auto o = t.observe();
    using Obs = decltype(o);
    if (auto *r = std::get_if<typename Obs::RetF>(&o.v())) return r->r;
    auto *s = std::get_if<typename Obs::TauF>(&o.v());
    Tree next = s->t;
    t = std::move(next);
  }
}
int main() {
  auto r = run(LoopifyResultNoDefault::sum_tree(std::monostate{}));
  std::cout << r << std::endl;
  return r == 10 ? 0 : 1;
}
