#ifndef INCLUDED_PAIRINDEXEDINDUCTIVEANYCAST
#define INCLUDED_PAIRINDEXEDINDUCTIVEANYCAST

#include <any>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace PairIndexedInductiveAnyCast {

struct Pair_wrap {
  // TYPES
  struct Mk_pair_wrap {
    std::any a;
  };

  using variant_t = std::variant<Mk_pair_wrap>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Pair_wrap() {}

  explicit Pair_wrap(Mk_pair_wrap _v) : v_(std::move(_v)) {}

  Pair_wrap(const Pair_wrap &_other) : v_(std::move(_other.clone().v_)) {}

  Pair_wrap(Pair_wrap &&_other) : v_(std::move(_other.v_)) {}

  Pair_wrap &operator=(const Pair_wrap &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Pair_wrap &operator=(Pair_wrap &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Pair_wrap clone() const {
    const auto &[a] = std::get<Mk_pair_wrap>(this->v());
    return Pair_wrap(Mk_pair_wrap{a});
  }

  // CREATORS
  static Pair_wrap mk_pair_wrap(std::any a) {
    return Pair_wrap(Mk_pair_wrap{std::move(a)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Ops {
  template <typename T1> static T1 get_fst(const Pair_wrap &p) {
    const auto &[a] = std::get<typename Pair_wrap::Mk_pair_wrap>(p.v());
    return std::any_cast<std::pair<T1, Datatypes::Nat>>(a).first;
  }

  template <typename T1> static Datatypes::Nat get_snd(const Pair_wrap &p) {
    const auto &[a] = std::get<typename Pair_wrap::Mk_pair_wrap>(p.v());
    return std::any_cast<std::pair<T1, Datatypes::Nat>>(a).second;
  }

  template <typename T1> static Pair_wrap make(T1 a, Datatypes::Nat n) {
    return Pair_wrap::mk_pair_wrap(std::make_pair(a, std::move(n)));
  }
};

} // namespace PairIndexedInductiveAnyCast

#endif // INCLUDED_PAIRINDEXEDINDUCTIVEANYCAST
