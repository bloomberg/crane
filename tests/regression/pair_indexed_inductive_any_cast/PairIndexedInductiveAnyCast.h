#ifndef INCLUDED_PAIRINDEXEDINDUCTIVEANYCAST
#define INCLUDED_PAIRINDEXEDINDUCTIVEANYCAST

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace PairIndexedInductiveAnyCast {

struct Pair_wrap;

struct Pair_wrap {
  // DATA
  crane::obj a;

  // ACCESSORS
  Pair_wrap clone() const { return {a}; }

  // CREATORS
  static Pair_wrap mk_pair_wrap(crane::obj a) { return {std::move(a)}; }
};

struct Ops {
  template <typename T1> static T1 get_fst(const Pair_wrap &p) {
    const auto &[a] = p;
    return crane_any_cast<std::pair<T1, Datatypes::Nat>>(a).first;
  }

  template <typename T1 = void>
  static Datatypes::Nat get_snd(const Pair_wrap &p) {
    const auto &[a] = p;
    return crane_any_cast<std::pair<T1, Datatypes::Nat>>(a).second;
  }

  template <typename T1>
  static Pair_wrap make(const T1 &a, const Datatypes::Nat &n) {
    return Pair_wrap::mk_pair_wrap(std::make_pair(a, n));
  }
};

} // namespace PairIndexedInductiveAnyCast

#endif // INCLUDED_PAIRINDEXEDINDUCTIVEANYCAST
