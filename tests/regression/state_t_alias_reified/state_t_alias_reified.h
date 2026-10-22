#ifndef INCLUDED_STATE_T_ALIAS_REIFIED
#define INCLUDED_STATE_T_ALIAS_REIFIED

#include "fn.h"
#include "shared_block.h"
#include <crane_itree.h>
#include <cstdint>
#include <memory>
#include <utility>

struct Monads {
  template <typename s, template <typename> class m, typename a>
  using stateT = crane::fn<m<std::pair<s, a>>(s)>;
};

template <typename CraneTcArg>
using itree_tc_609e8855cd7ad294 = std::shared_ptr<ITree<CraneTcArg>>;

struct StateTAliasReified {
  static inline const Monads::template stateT<
      uint64_t, itree_tc_609e8855cd7ad294, uint64_t>
      tick = [](uint64_t s) { return itree_ret(std::make_pair((s + 1), s)); };
  static Monads::template stateT<uint64_t, itree_tc_609e8855cd7ad294, uint64_t>
  twice(std::type_identity_t<
        Monads::template stateT<uint64_t, itree_tc_609e8855cd7ad294, uint64_t>>
            c);
  static std::shared_ptr<ITree<std::pair<uint64_t, uint64_t>>> run(uint64_t n);
  template <typename r> using M = std::shared_ptr<ITree<r>>;
  static inline const M<uint64_t> seed = itree_ret(UINT64_C(7));
  static M<uint64_t> plus_one(const std::shared_ptr<ITree<uint64_t>> &m);
  static inline const M<uint64_t> from_seed =
      itree_bind(seed, [](uint64_t x) { return plus_one(itree_ret(x)); });
  static M<uint64_t> seeded(uint64_t n);
};

#endif // INCLUDED_STATE_T_ALIAS_REIFIED
