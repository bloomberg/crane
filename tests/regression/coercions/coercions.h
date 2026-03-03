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
  static unsigned int bool_to_nat(const bool b);

  static unsigned int add_bool(const unsigned int n, const bool b);

  static inline const unsigned int test_add_true =
      add_bool((((((0 + 1) + 1) + 1) + 1) + 1), true);

  static inline const unsigned int test_add_false =
      add_bool((((((0 + 1) + 1) + 1) + 1) + 1), false);

  struct Wrapper {
    unsigned int unwrap;
  };

  static unsigned int unwrap(const std::shared_ptr<Wrapper> &w);

  static unsigned int double_wrapped(const std::shared_ptr<Wrapper> &w);

  static inline const unsigned int test_double_wrapped =
      double_wrapped(std::make_shared<Wrapper>(
          Wrapper{(((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1)}));

  struct BoolBox {
    bool unbox;
  };

  static bool unbox(const std::shared_ptr<BoolBox> &b);

  static unsigned int add_boolbox(const unsigned int n,
                                  const std::shared_ptr<BoolBox> &bb);

  static inline const unsigned int test_add_boolbox =
      add_boolbox(((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                  std::make_shared<BoolBox>(BoolBox{true}));

  struct Transform {
    std::function<unsigned int(unsigned int)> apply_transform;
  };

  static unsigned int apply_transform(const std::shared_ptr<Transform> &,
                                      const unsigned int);

  static inline const std::shared_ptr<Transform> double_transform =
      std::make_shared<Transform>(
          Transform{[](unsigned int n) { return (n + n); }});

  static inline const unsigned int test_fun_coercion =
      double_transform->apply_transform((((((0 + 1) + 1) + 1) + 1) + 1));
};
