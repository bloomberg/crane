#ifndef INCLUDED_SLLPAIRCAST
#define INCLUDED_SLLPAIRCAST

#include "obj.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace SllPairCast {

struct SllPairCast {
  struct sll_frame {
    std::optional<uint64_t> fr_ret;
    Datatypes::List<uint64_t> fr_suf;
  };

  using sll_stack = std::pair<sll_frame, Datatypes::List<sll_frame>>;

  struct sll_subparser {
    Datatypes::List<uint64_t> sll_pred;
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

} // namespace SllPairCast

#endif // INCLUDED_SLLPAIRCAST
