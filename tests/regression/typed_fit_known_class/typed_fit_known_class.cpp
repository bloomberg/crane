#include "typed_fit_known_class.h"

std::optional<uint64_t>
TypedFitKnownClass::answer(uint64_t fuel,
                           const Itree<TypedFitKnownClass::AskE, uint64_t> &t) {
  if (fuel <= 0) {
    return std::optional<uint64_t>();
  } else {
    uint64_t f = fuel - 1;
    auto &&_sv = t.observe();
    if (std::holds_alternative<
            typename ItreeF<TypedFitKnownClass::AskE, uint64_t,
                            Itree<TypedFitKnownClass::AskE, uint64_t>>::RetF>(
            _sv.v())) {
      const auto &[r0] = std::get<
          typename ItreeF<TypedFitKnownClass::AskE, uint64_t,
                          Itree<TypedFitKnownClass::AskE, uint64_t>>::RetF>(
          _sv.v());
      return std::make_optional<uint64_t>(r0);
    } else if (std::holds_alternative<typename ItreeF<
                   TypedFitKnownClass::AskE, uint64_t,
                   Itree<TypedFitKnownClass::AskE, uint64_t>>::TauF>(_sv.v())) {
      const auto &[t0] = std::get<
          typename ItreeF<TypedFitKnownClass::AskE, uint64_t,
                          Itree<TypedFitKnownClass::AskE, uint64_t>>::TauF>(
          _sv.v());
      return answer(f, t0);
    } else {
      const auto &[_, e] = std::get<
          typename ItreeF<TypedFitKnownClass::AskE, uint64_t,
                          Itree<TypedFitKnownClass::AskE, uint64_t>>::VisF>(
          _sv.v());
      return answer(f, e(UINT64_C(3)));
    }
  }
}

uint64_t TypedFitKnownClass::measure_list(const List<uint64_t> &l) {
  return TypedFitKnownClass::ML::template measure<uint64_t>(l);
}

crane::obj Function::Id_IFun(crane::obj e) { return e; }
