#include "generic_monad_result_rewrapped.h"

std::shared_ptr<ITree<Nat>> GenericMonadResultRewrapped::twice(Nat n) {
  return itree_ret(n.add(n));
}

/// The first argument of ITree.bind is a generic-monad call result, so it
/// is already a tree and must not be lifted again.
std::shared_ptr<ITree<List<Nat>>>
GenericMonadResultRewrapped::run(const List<Nat> &l) {
  return itree_bind(map_monad<Monad_itree<crane::obj>, Nat, Nat>(twice, l),
                    [](const List<Nat> &ys) { return itree_ret(ys); });
}

std::shared_ptr<ITree<List<Nat>>>
GenericMonadResultRewrapped::go(const List<Nat> &x0_) {
  return run(x0_);
}
