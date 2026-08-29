#include "SllPairCastDeque.h"

namespace SllPairCastDeque {

bool SllPairCastDeque::sll_final_config(
    const SllPairCastDeque::sll_subparser &sp) {
  std::any _x = sp.sll_pred;
  std::pair<SllPairCastDeque::sll_frame,
            std::deque<SllPairCastDeque::sll_frame>>
      sll_stk0 = sp.sll_stk;
  const auto &[s, l] = sll_stk0;
  std::optional<uint64_t> fr_ret0 = s.fr_ret;
  std::deque<uint64_t> fr_suf0 = s.fr_suf;
  if (fr_ret0.has_value()) {
    const uint64_t &_x0 = *fr_ret0;
    return false;
  } else {
    if (fr_suf0.empty()) {
      if (l.empty()) {
        return true;
      } else {
        const auto &_x0 = l.front();
        std::decay_t<decltype(l)> _x1(l.begin() + 1, l.end());
        return false;
      }
    } else {
      const auto &_x0 = fr_suf0.front();
      std::decay_t<decltype(fr_suf0)> _x1(fr_suf0.begin() + 1, fr_suf0.end());
      return false;
    }
  }
}

} // namespace SllPairCastDeque
