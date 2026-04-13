#ifndef INCLUDED_LOOPIFY_NUMERIC_MISC
#define INCLUDED_LOOPIFY_NUMERIC_MISC

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct LoopifyNumericMisc {
  __attribute__((pure)) static unsigned int
  sum_abs(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  alternating_ops(const unsigned int n);
  __attribute__((pure)) static unsigned int
  count_even(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  count_odd(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  product(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  sum_of_squares(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int max_two(const unsigned int a,
                                                    const unsigned int b);
  __attribute__((pure)) static unsigned int
  list_max(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  list_min(const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_NUMERIC_MISC
