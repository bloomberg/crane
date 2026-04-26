#ifndef INCLUDED_CLOSURE_RECURSIVE_BUILD
#define INCLUDED_CLOSURE_RECURSIVE_BUILD

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

struct ClosureRecursiveBuild {
  /// A list of closures, each one of which captures a different value.
  struct fn_list {
    // TYPES
    struct FNil {};

    struct FCons {
      std::function<unsigned int(unsigned int)> d_a0;
      std::unique_ptr<fn_list> d_a1;
    };

    using variant_t = std::variant<FNil, FCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    fn_list() {}

    explicit fn_list(FNil _v) : d_v_(_v) {}

    explicit fn_list(FCons _v) : d_v_(std::move(_v)) {}

    fn_list(const fn_list &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    fn_list(fn_list &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) fn_list &operator=(const fn_list &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) fn_list &operator=(fn_list &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) fn_list clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<FNil>(_sv.v())) {
        return fn_list(FNil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<FCons>(_sv.v());
        return fn_list(FCons{d_a0, clone_value(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static fn_list fnil() { return fn_list(FNil{}); }

    __attribute__((pure)) static fn_list
    fcons(std::function<unsigned int(unsigned int)> a0, const fn_list &a1) {
      return fn_list(FCons{std::move(a0), std::make_unique<fn_list>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) fn_list *operator->() { return this; }

    __attribute__((pure)) const fn_list *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = fn_list(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1,
      MapsTo<T1, std::function<unsigned int(unsigned int)>, fn_list, T1> F1>
  static T1 fn_list_rect(const T1 f, F1 &&f0, const fn_list &f1) {
    if (std::holds_alternative<typename fn_list::FNil>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename fn_list::FCons>(f1.v());
      return f0(d_a0, *(d_a1), fn_list_rect<T1>(f, f0, *(d_a1)));
    }
  }

  template <
      typename T1,
      MapsTo<T1, std::function<unsigned int(unsigned int)>, fn_list, T1> F1>
  static T1 fn_list_rec(const T1 f, F1 &&f0, const fn_list &f1) {
    if (std::holds_alternative<typename fn_list::FNil>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename fn_list::FCons>(f1.v());
      return f0(d_a0, *(d_a1), fn_list_rec<T1>(f, f0, *(d_a1)));
    }
  }

  /// Recursively build a list of fixpoint closures. Each recursive call
  /// creates a local fixpoint adder that captures the current n.
  ///
  /// BUG HYPOTHESIS: Each adder captures n from its stack frame
  /// by &. The closures are stored in FCons constructors. After
  /// build_adders returns, all intermediate stack frames are gone,
  /// and every closure holds a dangling reference.
  __attribute__((pure)) static fn_list build_adders(unsigned int n);
  __attribute__((pure)) static unsigned int apply_first(const fn_list &fl,
                                                        const unsigned int &x);
  __attribute__((pure)) static unsigned int
  apply_all_sum(const fn_list &fl, const unsigned int &x);
  /// test1: build_adders(3) = adder_3, adder_2, adder_1.
  /// apply_first returns adder_3(10) = 3 + 10 = 13.
  static inline const unsigned int test1 = apply_first(build_adders(3u), 10u);
  /// test2: apply_all_sum sums all adders applied to 0.
  /// adder_3(0) + adder_2(0) + adder_1(0) = 3 + 2 + 1 = 6.
  static inline const unsigned int test2 = apply_all_sum(build_adders(3u), 0u);
  /// test3: with noise between build and use.
  /// build_adders(5), noise, then apply_first(fns, 0) = 5.
  static inline const unsigned int test3 = []() {
    fn_list fns = build_adders(5u);
    unsigned int noise = ((99u + 88u) + 77u);
    return (apply_first(fns, 0u) + noise);
  }();
};

#endif // INCLUDED_CLOSURE_RECURSIVE_BUILD
