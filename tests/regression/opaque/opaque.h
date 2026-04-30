#ifndef INCLUDED_OPAQUE
#define INCLUDED_OPAQUE

#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_x;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Sig() {}

  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

  Sig(const Sig<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Sig(Sig<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Sig<t_A> &operator=(const Sig<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Sig<t_A> &operator=(Sig<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Sig<t_A> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x] = std::get<Exist>(_sv.v());
    return Sig<t_A>(Exist{d_x});
  }

  // CREATORS
  template <typename _U> explicit Sig(const Sig<_U> &_other) {
    const auto &[d_x] = std::get<typename Sig<_U>::Exist>(_other.v());
    d_v_ = Exist{t_A(d_x)};
  }

  static Sig<t_A> exist(t_A x) { return Sig(Exist{std::move(x)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct Opaque {
  static unsigned int safe_pred(const unsigned int &n);
  static unsigned int pred_of_succ(unsigned int n);
  static bool nat_eq_dec(const unsigned int &n, const unsigned int &x);
  static bool are_equal(const unsigned int &n, const unsigned int &m);
  static Sig<unsigned int> bounded_add(const unsigned int &_x0,
                                       const unsigned int &_x1,
                                       const unsigned int &_x2);
  static inline const unsigned int test_safe_pred = safe_pred(5u);
  static inline const unsigned int test_pred_succ = pred_of_succ(7u);
  static inline const bool test_eq_true = are_equal(5u, 5u);
  static inline const bool test_eq_false = are_equal(3u, 7u);
};

#endif // INCLUDED_OPAQUE
