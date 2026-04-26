#ifndef INCLUDED_PATHOLOGICAL_RECORD
#define INCLUDED_PATHOLOGICAL_RECORD

#include <any>
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

struct PathologicalRecord {
  struct Rec {
    unsigned int f1;
    unsigned int f2;
    unsigned int f3;

    __attribute__((pure)) Rec *operator->() { return this; }

    __attribute__((pure)) const Rec *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Rec clone() const {
      return Rec{(*(this)).f1, (*(this)).f2, (*(this)).f3};
    }
  };

  __attribute__((pure)) static unsigned int hof_access(const Rec &r);
  __attribute__((pure)) static unsigned int nested_lets(const Rec &r);
  __attribute__((pure)) static unsigned int
  conditional_access(const Rec &r, const bool &flag);
  __attribute__((pure)) static unsigned int countdown(const unsigned int &n,
                                                      const Rec &r);
  __attribute__((pure)) static unsigned int double_match(const Rec &r1,
                                                         const Rec &r2);
  __attribute__((pure)) static unsigned int
  closure_over_fields(const Rec &r, const unsigned int &x);
  static inline const unsigned int use_closure =
      closure_over_fields(Rec{1u, 2u, 3u}, 10u);
  __attribute__((pure)) static unsigned int guarded_pattern(const Rec &r);

  struct BigRec {
    unsigned int bf1;
    unsigned int bf2;
    unsigned int bf3;
    unsigned int bf4;
    unsigned int bf5;

    __attribute__((pure)) BigRec *operator->() { return this; }

    __attribute__((pure)) const BigRec *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) BigRec clone() const {
      return BigRec{(*(this)).bf1, (*(this)).bf2, (*(this)).bf3, (*(this)).bf4,
                    (*(this)).bf5};
    }
  };

  __attribute__((pure)) static unsigned int scrambled_access(const BigRec &r);
  __attribute__((pure)) static unsigned int repeated_access(const BigRec &r);
  static inline const unsigned int test1 = hof_access(Rec{1u, 2u, 3u});
  static inline const unsigned int test2 = nested_lets(Rec{4u, 5u, 6u});
  static inline const unsigned int test3 =
      double_match(Rec{1u, 2u, 3u}, Rec{4u, 5u, 6u});
};

#endif // INCLUDED_PATHOLOGICAL_RECORD
