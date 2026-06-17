#include "SllPairCast.h"

#include "Datatypes.h"

namespace SllPairCast {

bool SllPairCast::sll_final_config(const SllPairCast::sll_subparser &sp) {
  std::any _x = sp.sll_pred;
  std::pair<SllPairCast::sll_frame, Datatypes::List<SllPairCast::sll_frame>>
      sll_stk0 = sp.sll_stk;
  const auto &[s, l] =
      std::any_cast<std::pair<SllPairCast::sll_frame,
                              Datatypes::List<SllPairCast::sll_frame>>>(
          sll_stk0);
  std::optional<uint64_t> fr_ret0 =
      std::any_cast<SllPairCast::sll_frame>(s).fr_ret;
  Datatypes::List<uint64_t> fr_suf0 =
      std::any_cast<SllPairCast::sll_frame>(s).fr_suf;
  if (fr_ret0.has_value()) {
    const uint64_t &_x0 = *fr_ret0;
    return false;
  } else {
    if (std::holds_alternative<typename Datatypes::List<uint64_t>::Nil>(
            fr_suf0.v())) {
      if (std::holds_alternative<
              typename Datatypes::List<SllPairCast::sll_frame>::Nil>(l.v())) {
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  }
}

} // namespace SllPairCast
