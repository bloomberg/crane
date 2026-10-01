#include "stateT_dict_arg_dropped.h"

std::shared_ptr<ITree<std::pair<Nat, env>>>
StateTDictArgDropped::use(const Nat &n) {
  return crane_container_cast<std::shared_ptr<ITree<std::pair<Nat, env>>>>(
      twice<FailE>(n).runStateT(Nat::o()));
}
