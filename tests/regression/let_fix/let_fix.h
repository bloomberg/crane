#ifndef INCLUDED_LET_FIX
#define INCLUDED_LET_FIX

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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

struct LetFix {
  __attribute__((pure)) static unsigned int
  local_sum(const std::shared_ptr<List<unsigned int>> &l);

  template <typename T1>
  static std::shared_ptr<List<T1>>
  local_rev(const std::shared_ptr<List<T1>> &l) {
    std::function<std::shared_ptr<List<T1>>(std::shared_ptr<List<T1>>,
                                            std::shared_ptr<List<T1>>)>
        go;
    go = [&](std::shared_ptr<List<T1>> acc,
             std::shared_ptr<List<T1>> xs) -> std::shared_ptr<List<T1>> {
      if (std::holds_alternative<typename List<T1>::Nil>(xs->v())) {
        return acc;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(xs->v());
        return go(List<T1>::cons(d_a0, acc), d_a1);
      }
    };
    return go(List<T1>::nil(), l);
  }

  static std::shared_ptr<List<unsigned int>> local_flatten(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &xss);
  __attribute__((pure)) static bool
  local_mem(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);

  template <typename T1>
  __attribute__((pure)) static unsigned int
  local_length(const std::shared_ptr<List<T1>> &xs) {
    if (std::holds_alternative<typename List<T1>::Nil>(xs->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(xs->v());
      return (local_length<T1>(d_a1) + 1);
    }
  }

  static inline const unsigned int test_sum =
      local_sum(List<unsigned int>::cons(
          1u, List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(
                          3u, List<unsigned int>::cons(
                                  4u, List<unsigned int>::cons(
                                          5u, List<unsigned int>::nil()))))));
  static inline const std::shared_ptr<List<unsigned int>> test_rev =
      local_rev<unsigned int>(List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))));
  static inline const std::shared_ptr<List<unsigned int>> test_flatten =
      local_flatten(List<std::shared_ptr<List<unsigned int>>>::cons(
          List<unsigned int>::cons(
              1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())),
          List<std::shared_ptr<List<unsigned int>>>::cons(
              List<unsigned int>::cons(3u, List<unsigned int>::nil()),
              List<std::shared_ptr<List<unsigned int>>>::cons(
                  List<unsigned int>::cons(
                      4u, List<unsigned int>::cons(
                              5u, List<unsigned int>::cons(
                                      6u, List<unsigned int>::nil()))),
                  List<std::shared_ptr<List<unsigned int>>>::nil()))));
  static inline const bool test_mem_found = local_mem(
      3u, List<unsigned int>::cons(
              1u, List<unsigned int>::cons(
                      2u, List<unsigned int>::cons(
                              3u, List<unsigned int>::cons(
                                      4u, List<unsigned int>::nil())))));
  static inline const bool test_mem_missing = local_mem(
      9u, List<unsigned int>::cons(
              1u, List<unsigned int>::cons(
                      2u, List<unsigned int>::cons(
                              3u, List<unsigned int>::cons(
                                      4u, List<unsigned int>::nil())))));
  static inline const unsigned int test_length =
      local_length<unsigned int>(List<unsigned int>::cons(
          10u, List<unsigned int>::cons(
                   20u, List<unsigned int>::cons(
                            30u, List<unsigned int>::cons(
                                     40u, List<unsigned int>::nil())))));
};

#endif // INCLUDED_LET_FIX
