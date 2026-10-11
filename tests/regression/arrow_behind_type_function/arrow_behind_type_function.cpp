#include "arrow_behind_type_function.h"

uint64_t ArrowBehindTypeFunction::applyl(uint64_t n,
                                         ArrowBehindTypeFunction::nfun v,
                                         const List<uint64_t> &x) {
  if (n <= 0) {
    return crane::any_cast<uint64_t>(std::move(v));
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(x.v())) {
      return applyl(m,
                    crane::any_cast<crane::fn<crane::obj(crane::obj)>>(
                        std::move(v))(UINT64_C(0)),
                    List<uint64_t>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(x.v());
      return applyl(
          m,
          crane::any_cast<crane::fn<crane::obj(crane::obj)>>(std::move(v))(a0),
          *a1);
    }
  }
}
