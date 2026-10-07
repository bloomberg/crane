#include "shared_variant_nested.h"

uint64_t SharedVariantNested::ssize(const SharedVariantNested::stmt &s) {
  if (crane::holds_alternative<typename SharedVariantNested::stmt::Assign>(
          s.v())) {
    const auto &[a0, a1] =
        crane::get<typename SharedVariantNested::stmt::Assign>(s.v());
    return (UINT64_C(1) + esize(*a1));
  } else if (crane::holds_alternative<typename SharedVariantNested::stmt::Seq>(
                 s.v())) {
    const auto &[a0, a1] =
        crane::get<typename SharedVariantNested::stmt::Seq>(s.v());
    return (ssize(*a0) + ssize(*a1));
  } else {
    return UINT64_C(1);
  }
}

uint64_t SharedVariantNested::esize(const SharedVariantNested::expr &e) {
  if (crane::holds_alternative<typename SharedVariantNested::expr::Num>(
          e.v())) {
    return UINT64_C(1);
  } else if (crane::holds_alternative<typename SharedVariantNested::expr::Add>(
                 e.v())) {
    const auto &[a0, a1] =
        crane::get<typename SharedVariantNested::expr::Add>(e.v());
    return (esize(*a0) + esize(*a1));
  } else {
    const auto &[a0, a1] =
        crane::get<typename SharedVariantNested::expr::Block>(e.v());
    return (ssize(*a0) + esize(*a1));
  }
}
