#ifndef INCLUDED_OPAQUE
#define INCLUDED_OPAQUE

#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct Sig {
  // TYPES
  struct Exist {
    A x;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sig() {}

  explicit Sig(Exist _v) : v_(std::move(_v)) {}

  Sig(const Sig<A> &_other) : v_(std::move(_other.clone().v_)) {}

  Sig(Sig<A> &&_other) : v_(std::move(_other.v_)) {}

  Sig<A> &operator=(const Sig<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Sig<A> &operator=(Sig<A> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Sig<A> clone() const {
    const auto &[x] = std::get<Exist>(this->v());
    return Sig<A>(Exist{x});
  }

  // CREATORS
  template <typename _U> explicit Sig(const Sig<_U> &_other) {
    const auto &[x] = std::get<typename Sig<_U>::Exist>(_other.v());
    this->v_ = Exist{A(x)};
  }

  static Sig<A> exist(A x) { return Sig(Exist{std::move(x)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Opaque {
  static unsigned int safe_pred(unsigned int n);
  static unsigned int pred_of_succ(unsigned int n);
  static bool nat_eq_dec(unsigned int n, unsigned int x);
  static bool are_equal(unsigned int n, unsigned int m);
  static Sig<unsigned int> bounded_add(unsigned int _x0, unsigned int _x1,
                                       unsigned int _x2);
  static inline const unsigned int test_safe_pred = safe_pred(5u);
  static inline const unsigned int test_pred_succ = pred_of_succ(7u);
  static inline const bool test_eq_true = are_equal(5u, 5u);
  static inline const bool test_eq_false = are_equal(3u, 7u);
};

#endif // INCLUDED_OPAQUE
