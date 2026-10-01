#include "handler_loop_call_drops_result_targ.h"

std::shared_ptr<ITree<Sum<Denot::template exc<typename natParams::ptr>, Nat>>>
HandlerLoopCallDropsResultTarg::run() {
  return Denot::template run_exc<natParams, Nat>(
      itree_ret(Nat::s(Nat::s(Nat::s(Nat::o())))));
}
