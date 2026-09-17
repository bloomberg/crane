#include "undeducible_tt_return.h"

std::optional<Nat> UndeducibleTtReturn::use(const Sum1<ReqA, ReqB, Nat> &ab) {
  return Handler::case_(
      [](const auto &e) {
        const auto &[x0] = e;
        return std::make_optional<Nat>(x0);
      },
      [](const auto &b) {
        const auto &[x0] = b;
        return std::make_optional<Nat>(x0);
      },
      ab);
}
