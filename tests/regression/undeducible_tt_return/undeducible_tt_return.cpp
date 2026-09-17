#include "undeducible_tt_return.h"

std::optional<Nat> UndeducibleTtReturn::use(const Sum1<ReqA, ReqB, Nat> &ab) {
  return Handler::case_(
      []<typename _X>(const ReqA<_X> &e) {
        const auto &[x0] = e;
        return std::make_optional<_X>(_X(x0));
      },
      []<typename _X>(const ReqB<_X> &b) {
        const auto &[x0] = b;
        return std::make_optional<_X>(_X(x0));
      },
      ab);
}
