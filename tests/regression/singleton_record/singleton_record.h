#ifndef INCLUDED_SINGLETON_RECORD
#define INCLUDED_SINGLETON_RECORD

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct SingletonRecord {
  struct wrapper {
    unsigned int value;

    __attribute__((pure)) wrapper *operator->() { return this; }

    __attribute__((pure)) const wrapper *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) wrapper clone() const {
      return wrapper{(*(this)).value};
    }
  };

  static inline const wrapper wrapped_five = wrapper{5u};
  __attribute__((pure)) static unsigned int get_value(const wrapper &w);
  __attribute__((pure)) static unsigned int get_value2(const wrapper &w);
  __attribute__((pure)) static unsigned int unwrap(const wrapper &w);
  __attribute__((pure)) static wrapper double_wrapped(const wrapper &w);

  template <typename t_A> struct box {
    t_A contents;

    __attribute__((pure)) box<t_A> *operator->() { return this; }

    __attribute__((pure)) const box<t_A> *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) box<t_A> clone() const {
      return box<t_A>{(*(this)).contents};
    }
  };

  static inline const box<unsigned int> boxed_three = box<unsigned int>{3u};

  template <typename T1> static T1 unbox(const box<T1> &b) {
    return b.contents;
  }

  static inline const box<box<unsigned int>> nested_box =
      box<box<unsigned int>>{boxed_three};
  static inline const unsigned int double_unbox = nested_box.contents.contents;

  struct fn_wrapper {
    std::function<unsigned int(unsigned int)> fn;

    __attribute__((pure)) fn_wrapper *operator->() { return this; }

    __attribute__((pure)) const fn_wrapper *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) fn_wrapper clone() const {
      return fn_wrapper{(*(this)).fn};
    }
  };

  static inline const fn_wrapper my_fn_wrapper =
      fn_wrapper{[](unsigned int _x0) -> unsigned int { return (1u + _x0); }};
  __attribute__((pure)) static unsigned int
  apply_wrapped(const fn_wrapper &w, const unsigned int &n);
  static inline const unsigned int test_get = get_value(wrapped_five);
  static inline const unsigned int test_get2 = get_value2(wrapped_five);
  static inline const unsigned int test_unwrap = unwrap(wrapped_five);
  static inline const unsigned int test_double =
      double_wrapped(wrapped_five).value;
  static inline const unsigned int test_unbox =
      unbox<unsigned int>(boxed_three);
  static inline const unsigned int test_double_unbox = double_unbox;
  static inline const unsigned int test_fn = apply_wrapped(my_fn_wrapper, 7u);
};

#endif // INCLUDED_SINGLETON_RECORD
