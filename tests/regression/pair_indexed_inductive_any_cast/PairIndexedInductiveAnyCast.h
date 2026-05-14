#ifndef INCLUDED_PAIRINDEXEDINDUCTIVEANYCAST
#define INCLUDED_PAIRINDEXEDINDUCTIVEANYCAST

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace PairIndexedInductiveAnyCast {

struct Pair_wrap {
  // TYPES
  struct Mk_pair_wrap {
    std::any d_a;
  };

  using variant_t = std::variant<Mk_pair_wrap>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Pair_wrap() {}

  explicit Pair_wrap(Mk_pair_wrap _v) : d_v_(std::move(_v)) {}

  Pair_wrap(const Pair_wrap &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Pair_wrap(Pair_wrap &&_other) : d_v_(std::move(_other.d_v_)) {}

  Pair_wrap &operator=(const Pair_wrap &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Pair_wrap &operator=(Pair_wrap &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Pair_wrap clone() const {
    auto &&_sv = *(this);
    const auto &[d_a] = std::get<Mk_pair_wrap>(_sv.v());
    return Pair_wrap(Mk_pair_wrap(d_a));
  }

  // CREATORS
  static Pair_wrap mk_pair_wrap(std::any a) {
    return Pair_wrap(Mk_pair_wrap(std::move(a)));
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct Ops {
  template <typename T1> static T1 get_fst(const Pair_wrap &p) {
    const auto &[d_a] = std::get<typename Pair_wrap::Mk_pair_wrap>(p.v());
    return std::any_cast<std::pair<T1, Datatypes::Nat>>(d_a).first;
  }

  template <typename T1> static Datatypes::Nat get_snd(const Pair_wrap &p) {
    const auto &[d_a] = std::get<typename Pair_wrap::Mk_pair_wrap>(p.v());
    return std::any_cast<std::pair<T1, Datatypes::Nat>>(d_a).second;
  }

  template <typename T1> static Pair_wrap make(T1 a, Datatypes::Nat n) {
    return Pair_wrap::mk_pair_wrap(std::make_pair(a, std::move(n)));
  }
};

} // namespace PairIndexedInductiveAnyCast

#endif // INCLUDED_PAIRINDEXEDINDUCTIVEANYCAST
