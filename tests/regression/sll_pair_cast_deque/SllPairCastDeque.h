#ifndef INCLUDED_SLLPAIRCASTDEQUE
#define INCLUDED_SLLPAIRCASTDEQUE

#include "obj.h"
#include <cstdint>
#include <deque>
#include <memory>
#include <optional>
#include <utility>

namespace SllPairCastDeque {

struct SllPairCastDeque {
  struct sll_frame {
    std::optional<uint64_t> fr_ret;
    std::deque<uint64_t> fr_suf;
  };

  using sll_stack = std::pair<sll_frame, std::deque<sll_frame>>;

  struct sll_subparser {
    std::deque<uint64_t> sll_pred;
    sll_stack sll_stk;
  };

  static bool sll_final_config(const sll_subparser &sp);

  static const bool &test_final() {
    static const bool v = true;
    return v;
  }

  static const bool &test_not_final() {
    static const bool v = false;
    return v;
  }
};

} // namespace SllPairCastDeque

#endif // INCLUDED_SLLPAIRCASTDEQUE
