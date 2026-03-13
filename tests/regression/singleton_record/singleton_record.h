#ifndef INCLUDED_SINGLETON_RECORD
#define INCLUDED_SINGLETON_RECORD

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

struct SingletonRecord {
  struct wrapper {
    unsigned int value;
  };

  static inline const std::shared_ptr<wrapper> wrapped_five =
      std::make_shared<wrapper>(wrapper{5u});
  __attribute__((pure)) static unsigned int
  get_value(const std::shared_ptr<wrapper> &w);
  __attribute__((pure)) static unsigned int
  get_value2(const std::shared_ptr<wrapper> &w);
  __attribute__((pure)) static unsigned int
  unwrap(const std::shared_ptr<wrapper> &w);
  static std::shared_ptr<wrapper> double_wrapped(std::shared_ptr<wrapper> w);

  template <typename t_A> struct box {
    t_A contents;
  };

  static inline const std::shared_ptr<box<unsigned int>> boxed_three =
      std::make_shared<box<unsigned int>>(box<unsigned int>{3u});

  template <typename T1> static T1 unbox(const std::shared_ptr<box<T1>> &b) {
    return b->contents;
  }

  static inline const std::shared_ptr<box<std::shared_ptr<box<unsigned int>>>>
      nested_box = std::make_shared<box<std::shared_ptr<box<unsigned int>>>>(
          box<std::shared_ptr<box<unsigned int>>>{boxed_three});
  static inline const unsigned int double_unbox =
      nested_box->contents->contents;

  struct fn_wrapper {
    std::function<unsigned int(unsigned int)> fn;
  };

  static inline const std::shared_ptr<fn_wrapper> my_fn_wrapper =
      std::make_shared<fn_wrapper>(fn_wrapper{
          [](unsigned int _x0) -> unsigned int { return (1u + _x0); }});
  __attribute__((pure)) static unsigned int
  apply_wrapped(const std::shared_ptr<fn_wrapper> &w, const unsigned int n);
  static inline const unsigned int test_get = get_value(wrapped_five);
  static inline const unsigned int test_get2 = get_value2(wrapped_five);
  static inline const unsigned int test_unwrap = unwrap(wrapped_five);
  static inline const unsigned int test_double =
      double_wrapped(wrapped_five)->value;
  static inline const unsigned int test_unbox =
      unbox<unsigned int>(boxed_three);
  static inline const unsigned int test_double_unbox = double_unbox;
  static inline const unsigned int test_fn = apply_wrapped(my_fn_wrapper, 7u);
};

#endif // INCLUDED_SINGLETON_RECORD
