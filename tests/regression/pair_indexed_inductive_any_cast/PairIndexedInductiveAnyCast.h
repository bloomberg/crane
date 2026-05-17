#ifndef INCLUDED_PAIRINDEXEDINDUCTIVEANYCAST
#define INCLUDED_PAIRINDEXEDINDUCTIVEANYCAST

#include <any>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace PairIndexedInductiveAnyCast {

struct Pair_wrap {
  // DATA
  std::any a;

  // ACCESSORS
  Pair_wrap clone() const { return {a}; }

  // CREATORS
  static Pair_wrap mk_pair_wrap(std::any a) { return {std::move(a)}; }
};

struct Ops {
  template <typename T1> static T1 get_fst(const Pair_wrap &p) {
    const auto &[a] = p;
    return std::any_cast<std::pair<T1, Datatypes::Nat>>(a).first;
  }

  template <typename T1> static Datatypes::Nat get_snd(const Pair_wrap &p) {
    const auto &[a] = p;
    return std::any_cast<std::pair<T1, Datatypes::Nat>>(a).second;
  }

  template <typename T1> static Pair_wrap make(T1 a, Datatypes::Nat n) {
    return Pair_wrap::mk_pair_wrap(std::make_pair(a, std::move(n)));
  }
};

} // namespace PairIndexedInductiveAnyCast

#endif // INCLUDED_PAIRINDEXEDINDUCTIVEANYCAST
