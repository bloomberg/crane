#include "mrec_ctx_wrapped_in_ret.h"

std::shared_ptr<ITree<Nat>> MrecCtxWrappedInRet::run() {
  return Recursion::template mrec<CountE, std::any, Nat>(
      []() {
        return [](CountE _x0) -> std::shared_ptr<ITree<std::any>> {
          return _x0.ctx(false);
        };
      }(),
      CountE::count(Nat::s(Nat::s(Nat::s(Nat::o())))));
}
