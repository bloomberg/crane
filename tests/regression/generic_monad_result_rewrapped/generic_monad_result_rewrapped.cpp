#include "generic_monad_result_rewrapped.h"

std::shared_ptr<ITree<List<Nat>>>
GenericMonadResultRewrapped::go(const List<Nat> &x0_) {
  return run<E1>(x0_);
}
