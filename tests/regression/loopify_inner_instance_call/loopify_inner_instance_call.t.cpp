#include <loopify_inner_instance_call.h>
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
  bool ok = run(LoopifyInnerInstanceCall::check(std::monostate{}));
  std::cout << (ok ? "ok" : "wrong") << std::endl;
  return ok ? 0 : 1;
}
