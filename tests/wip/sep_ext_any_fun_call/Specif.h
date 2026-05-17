#ifndef INCLUDED_SPECIF
#define INCLUDED_SPECIF

#include <utility>
#include <variant>

namespace Specif {

template <typename A, typename P> struct SigT {
  // TYPES
  struct ExistT {
    A x;
    P a1;
  };

  using variant_t = std::variant<ExistT>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  SigT() {}

  explicit SigT(ExistT _v) : v_(std::move(_v)) {}

  SigT(const SigT<A, P> &_other) : v_(std::move(_other.clone().v_)) {}

  SigT(SigT<A, P> &&_other) : v_(std::move(_other.v_)) {}

  SigT<A, P> &operator=(const SigT<A, P> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  SigT<A, P> &operator=(SigT<A, P> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  SigT<A, P> clone() const {
    const auto &[x, a1] = std::get<ExistT>(this->v());
    return SigT<A, P>(ExistT{x, a1});
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit SigT(const SigT<_U0, _U1> &_other) {
    const auto &[x, a1] = std::get<typename SigT<_U0, _U1>::ExistT>(_other.v());
    this->v_ = ExistT{A(x), P(a1)};
  }

  static SigT<A, P> existt(A x, P a1) {
    return SigT(ExistT{std::move(x), std::move(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  P projT2() const {
    const auto &[x0, a1] = std::get<typename SigT<A, P>::ExistT>(this->v());
    return a1;
  }
};

} // namespace Specif

#endif // INCLUDED_SPECIF
