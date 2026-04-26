#ifndef INCLUDED_RECORD_PROJ
#define INCLUDED_RECORD_PROJ

#include <memory>
#include <optional>
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

struct RecordProj {
  struct Point {
    unsigned int x;
    unsigned int y;

    __attribute__((pure)) Point *operator->() { return this; }

    __attribute__((pure)) const Point *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Point clone() const {
      return Point{(*(this)).x, (*(this)).y};
    }
  };

  struct ComplexRecord {
    unsigned int field1;
    unsigned int field2;
    unsigned int field3;

    __attribute__((pure)) ComplexRecord *operator->() { return this; }

    __attribute__((pure)) const ComplexRecord *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) ComplexRecord clone() const {
      return ComplexRecord{(*(this)).field1, (*(this)).field2,
                           (*(this)).field3};
    }
  };

  __attribute__((pure)) static unsigned int weird_access(const Point &p);
  __attribute__((pure)) static unsigned int
  complex_access(const ComplexRecord &c);
  __attribute__((pure)) static unsigned int
  nested_record_match(const Point &p1, const Point &p2);

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int apply_to_field(F0 &&f,
                                                           const Point &p) {
    unsigned int a = p.x;
    unsigned int b = p.y;
    return (f(a) + f(b));
  }

  static inline const unsigned int test1 = weird_access(Point{10u, 20u});
  static inline const unsigned int test2 =
      complex_access(ComplexRecord{5u, 10u, 15u});
};

#endif // INCLUDED_RECORD_PROJ
