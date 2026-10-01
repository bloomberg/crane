#include "mrec_ctx_wrapped_in_ret.h"

std::shared_ptr<ITree<Nat>> MrecCtxWrappedInRet::run() {
  return run_mrec<natParams>();
}
