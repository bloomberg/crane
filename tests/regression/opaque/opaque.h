#ifndef INCLUDED_OPAQUE
#define INCLUDED_OPAQUE

#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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
  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Sig<t_A>> exist(t_A x) {
    return std::make_shared<Sig<t_A>>(Exist{std::move(x)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Opaque {
  __attribute__((pure)) static unsigned int safe_pred(const unsigned int n);
  __attribute__((pure)) static unsigned int pred_of_succ(const unsigned int n);
  __attribute__((pure)) static bool nat_eq_dec(const unsigned int n,
                                               const unsigned int x);
  __attribute__((pure)) static bool are_equal(const unsigned int n,
                                              const unsigned int m);
  static std::shared_ptr<Sig<unsigned int>> bounded_add(const unsigned int _x0,
                                                        const unsigned int _x1,
                                                        const unsigned int _x2);
  static inline const unsigned int test_safe_pred = safe_pred(5u);
  static inline const unsigned int test_pred_succ = pred_of_succ(7u);
  static inline const bool test_eq_true = are_equal(5u, 5u);
  static inline const bool test_eq_false = are_equal(3u, 7u);
};

#endif // INCLUDED_OPAQUE
