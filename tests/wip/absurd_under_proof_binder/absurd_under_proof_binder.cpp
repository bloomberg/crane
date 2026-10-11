#include "absurd_under_proof_binder.h"

uint64_t AbsurdUnderProofBinder::hd(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return app<uint64_t>(UINT64_C(0), UINT64_C(0), ([]() -> crane::obj {
                           throw std::logic_error("absurd case");
                         })());
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return a0;
  }
}
