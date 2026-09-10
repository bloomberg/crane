#include "sig_prop_comment.h"

uint64_t
SigSubset::head(const Sig<SigSubset::lst> &p) { // Precondition: match l with
  // | SigSubset.nil => False
  // | SigSubset.cons _ _ => True
  // end
  return [=]() mutable {
    auto &&_sv = [=]() mutable {
      const auto &[x0] = p;
      return x0;
    }();
    if (std::holds_alternative<typename SigSubset::lst::Nil>(_sv.v())) {
      throw std::logic_error("absurd case");
    } else {
      const auto &[a0, a1] = std::get<typename SigSubset::lst::Cons>(_sv.v());
      return a0;
    }
  }();
}
