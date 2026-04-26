#ifndef INCLUDED_VALUE_TYPE_MATCH_FIX
#define INCLUDED_VALUE_TYPE_MATCH_FIX

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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

struct ValueTypeMatchFix {
  /// A non-recursive inductive (will be a value type).
  struct triple {
    // TYPES
    struct MkTriple {
      unsigned int d_a0;
      unsigned int d_a1;
      unsigned int d_a2;
    };

    using variant_t = std::variant<MkTriple>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    triple() {}

    explicit triple(MkTriple _v) : d_v_(std::move(_v)) {}

    triple(const triple &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    triple(triple &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) triple &operator=(const triple &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) triple &operator=(triple &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) triple clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] = std::get<MkTriple>(_sv.v());
      return triple(MkTriple{d_a0, d_a1, d_a2});
    }

    // CREATORS
    __attribute__((pure)) static triple
    mktriple(unsigned int a0, unsigned int a1, unsigned int a2) {
      return triple(MkTriple{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) triple *operator->() { return this; }

    __attribute__((pure)) const triple *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = triple(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1,
            MapsTo<T1, unsigned int, unsigned int, unsigned int> F0>
  static T1 triple_rect(F0 &&f, const triple &t) {
    const auto &[d_a0, d_a1, d_a2] = std::get<typename triple::MkTriple>(t.v());
    return f(d_a0, d_a1, d_a2);
  }

  template <typename T1,
            MapsTo<T1, unsigned int, unsigned int, unsigned int> F0>
  static T1 triple_rec(F0 &&f, const triple &t) {
    const auto &[d_a0, d_a1, d_a2] = std::get<typename triple::MkTriple>(t.v());
    return f(d_a0, d_a1, d_a2);
  }

  /// A fixpoint that captures a field from a value-type match.
  ///
  /// BUG HYPOTHESIS: triple is a value type (stack-allocated, non-recursive).
  /// When pattern matching on a value type, the fields are bound as
  /// references into the stack-allocated object. If a fixpoint captures
  /// these references by & and then escapes, the references dangle
  /// when the function returns and the value type is destroyed.
  ///
  /// This is different from pointer-based (shared_ptr) types where the
  /// field data lives on the heap and persists as long as the shared_ptr.
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  make_adder_from_triple(const triple &t);
  /// test1: MkTriple 10 20 30 -> base=60, go(5) = 60+5 = 65.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = make_adder_from_triple(triple::mktriple(10u, 20u, 30u));
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(5u);
    } else {
      return 999u;
    }
  }();
  /// test2: With noise between creation and use.
  static inline const unsigned int test2 = []() {
    std::optional<std::function<unsigned int(unsigned int)>> o =
        make_adder_from_triple(triple::mktriple(100u, 200u, 300u));
    unsigned int noise = (42u + 13u);
    if (o.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *o;
      return (f(0u) + noise);
    } else {
      return 999u;
    }
  }();
  /// Direct capture of pattern fields (no intermediate let binding).
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  make_field_adder(const triple &t);
  /// test3: MkTriple 42 0 0 -> a=42, go(3) = 42+3 = 45.
  static inline const unsigned int test3 = []() -> unsigned int {
    auto _cs = make_field_adder(triple::mktriple(42u, 0u, 0u));
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(3u);
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_VALUE_TYPE_MATCH_FIX
