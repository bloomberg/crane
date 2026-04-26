#ifndef INCLUDED_PRIM_ARRAY
#define INCLUDED_PRIM_ARRAY

#include <cstdint>
#include <memory>
#include <optional>
#include <persistent_array.h>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct PrimArray {
  static inline const persistent_array<unsigned int> arr5 =
      persistent_array<unsigned int>(int64_t(5), 0u);
  static inline const unsigned int get_default = arr5.get(int64_t(0));
  static inline const int64_t arr5_len = arr5.length();
  static inline const persistent_array<unsigned int> arr5_modified =
      arr5.set(int64_t(2), 42u);
  static inline const unsigned int get_modified = arr5_modified.get(int64_t(2));
  static inline const unsigned int get_original = arr5.get(int64_t(2));
  static inline const persistent_array<unsigned int> arr_chain =
      ((arr5.set(int64_t(0), 10u)).set(int64_t(1), 20u)).set(int64_t(2), 30u);
  static inline const unsigned int chain_0 = arr_chain.get(int64_t(0));
  static inline const unsigned int chain_1 = arr_chain.get(int64_t(1));
  static inline const unsigned int chain_2 = arr_chain.get(int64_t(2));
  static inline const unsigned int chain_3 = arr_chain.get(int64_t(3));
  static inline const persistent_array<unsigned int> arr_copy =
      arr5_modified.copy();
  static inline const unsigned int copy_val = arr_copy.get(int64_t(2));
  static inline const unsigned int oob_get = arr5.get(int64_t(99));
};

#endif // INCLUDED_PRIM_ARRAY
