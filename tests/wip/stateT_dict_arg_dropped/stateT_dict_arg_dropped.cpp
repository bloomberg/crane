#include "stateT_dict_arg_dropped.h"

stateT<env, std::shared_ptr<ITree<crane::obj>>, Nat> step(Nat n) {
  return stateT<Nat, std::shared_ptr<ITree<crane::obj>>, Nat>{
      [=, n = std::move(n)](const Nat &s) {
        return itree_ret(std::make_pair(n, s));
      }};
}

stateT<env, std::shared_ptr<ITree<crane::obj>>, Nat> twice(Nat n) {
  return Monad_stateT<Monad_itree<crane::obj>, env>::template bind<Nat, Nat>(
      step(std::move(n)), [](Nat a) {
        return Monad_stateT<Monad_itree<crane::obj>, env>::template bind<Nat,
                                                                         Nat>(
            step(std::move(a)), [](const Nat &b) {
              return Monad_stateT<Monad_itree<crane::obj>, env>::template ret<
                  Nat>(b);
            });
      });
}

std::shared_ptr<ITree<std::pair<Nat, env>>> StateTDictArgDropped::use(Nat n) {
  return crane_container_cast<std::shared_ptr<ITree<std::pair<Nat, env>>>>(
      twice(std::move(n)).runStateT(Nat::o()));
}
