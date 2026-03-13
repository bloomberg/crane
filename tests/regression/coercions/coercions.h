#ifndef INCLUDED_COERCIONS
#define INCLUDED_COERCIONS

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Coercions {
  __attribute__((pure)) static unsigned int bool_to_nat(const bool b);
  __attribute__((pure)) static unsigned int add_bool(const unsigned int n,
                                                     const bool b);
  static inline const unsigned int test_add_true = add_bool(5u, true);
  static inline const unsigned int test_add_false = add_bool(5u, false);

  struct Wrapper {
    unsigned int unwrap;
  };

  __attribute__((pure)) static unsigned int
  double_wrapped(const std::shared_ptr<Wrapper> &w);
  static inline const unsigned int test_double_wrapped =
      double_wrapped(std::make_shared<Wrapper>(Wrapper{7u}));

  struct BoolBox {
    bool unbox;
  };

  __attribute__((pure)) static unsigned int
  add_boolbox(const unsigned int n, const std::shared_ptr<BoolBox> &bb);
  static inline const unsigned int test_add_boolbox =
      add_boolbox(10u, std::make_shared<BoolBox>(BoolBox{true}));

  struct Transform {
    std::function<unsigned int(unsigned int)> apply_transform;
  };

  static inline const std::shared_ptr<Transform> double_transform =
      std::make_shared<Transform>(
          Transform{[](unsigned int n) { return (n + n); }});
  static inline const unsigned int test_fun_coercion =
      double_transform->apply_transform(5u);
};

#endif // INCLUDED_COERCIONS
