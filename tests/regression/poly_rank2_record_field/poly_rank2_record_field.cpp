#include "poly_rank2_record_field.h"

List<Bool0> PolyRank2RecordField::test1(const List<Nat> &l) {
  return run<Nat, Bool0>(m, [](const Nat &x) { return x.eqb(Nat::o()); }, l);
}

List<Nat> PolyRank2RecordField::test2(const List<Bool0> &l) {
  return run<Bool0, Nat>(
      m,
      [](Bool0 b) {
        switch (b) {
        case Bool0::TRUE_: {
          return Nat::s(Nat::o());
        }
        case Bool0::FALSE_: {
          return Nat::o();
        }
        default:
          std::unreachable();
        }
      },
      l);
}
