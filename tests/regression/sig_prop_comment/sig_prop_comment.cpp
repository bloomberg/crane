#include "sig_prop_comment.h"

uint64_t SigSubset::head(const SigSubset::lst &p) {
  // Precondition: match l with
  // | SigSubset.nil => False
  // | SigSubset.cons _ _ => True
  // end
  if (std::holds_alternative<typename SigSubset::lst::Nil>(p.v())) {
    throw std::logic_error("absurd case");
  } else {
    const auto &[a0, _] = std::get<typename SigSubset::lst::Cons>(p.v());
    return a0;
  }
}
