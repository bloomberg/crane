#ifndef INCLUDED_SINGLETON_RECORD
#define INCLUDED_SINGLETON_RECORD

#include <functional>

struct SingletonRecord {
  struct wrapper {
    uint64_t value;
  };

  static inline const wrapper wrapped_five = wrapper{UINT64_C(5)};
  static uint64_t get_value(const wrapper &w);
  static uint64_t get_value2(const wrapper &w);
  static uint64_t unwrap(const wrapper &w);
  static wrapper double_wrapped(const wrapper &w);

  template <typename A> struct box {
    A contents;
  };

  static inline const box<uint64_t> boxed_three = box<uint64_t>{UINT64_C(3)};

  template <typename T1> static T1 unbox(const box<T1> &b) {
    return b.contents;
  }

  static inline const box<box<uint64_t>> nested_box =
      box<box<uint64_t>>{boxed_three};
  static inline const uint64_t double_unbox = nested_box.contents.contents;

  struct fn_wrapper {
    std::function<uint64_t(uint64_t)> fn;
  };

  static inline const fn_wrapper my_fn_wrapper =
      fn_wrapper{[](uint64_t _x0) -> uint64_t { return (UINT64_C(1) + _x0); }};
  static uint64_t apply_wrapped(const fn_wrapper &w, uint64_t n);
  static inline const uint64_t test_get = get_value(wrapped_five);
  static inline const uint64_t test_get2 = get_value2(wrapped_five);
  static inline const uint64_t test_unwrap = unwrap(wrapped_five);
  static inline const uint64_t test_double = double_wrapped(wrapped_five).value;
  static inline const uint64_t test_unbox = unbox<uint64_t>(boxed_three);
  static inline const uint64_t test_double_unbox = double_unbox;
  static inline const uint64_t test_fn =
      apply_wrapped(my_fn_wrapper, UINT64_C(7));
};

#endif // INCLUDED_SINGLETON_RECORD
