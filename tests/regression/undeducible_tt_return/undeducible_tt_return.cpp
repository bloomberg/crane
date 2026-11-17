#include "undeducible_tt_return.h"

std::optional<Nat> UndeducibleTtReturn::use(
    const Sum1<ReqA<crane::obj>, ReqB<crane::obj>, Nat> &ab) {
  return Handler::template case_<ReqA<crane::obj>, ReqB<crane::obj>, Nat>(
      []<typename CraneX>(const ReqA<CraneX> &e) {
        const auto &[x0] = e;
        return std::make_optional<CraneX>(CraneX(x0));
      },
      []<typename CraneX>(const ReqB<CraneX> &b) {
        const auto &[x0] = b;
        return std::make_optional<CraneX>(CraneX(x0));
      },
      ab);
}
