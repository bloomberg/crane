#ifndef INCLUDED_COUNT_LOOP_TEST_TARGET
#define INCLUDED_COUNT_LOOP_TEST_TARGET

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

struct CountLoopTestTarget {
  struct instruction {
    // TYPES
    struct ISZ {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct NOP {};

    using variant_t = std::variant<ISZ, NOP>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    instruction() {}

    explicit instruction(ISZ _v) : d_v_(std::move(_v)) {}

    explicit instruction(NOP _v) : d_v_(_v) {}

    instruction(const instruction &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instruction(instruction &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) instruction &operator=(const instruction &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) instruction &operator=(instruction &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instruction clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<ISZ>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<ISZ>(_sv.v());
        return instruction(ISZ{d_a0, d_a1});
      } else {
        return instruction(NOP{});
      }
    }

    // CREATORS
    __attribute__((pure)) static instruction isz(unsigned int a0,
                                                 unsigned int a1) {
      return instruction(ISZ{std::move(a0), std::move(a1)});
    }

    constexpr static instruction nop() { return instruction(NOP{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) instruction *operator->() { return this; }

    __attribute__((pure)) const instruction *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = instruction(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 instruction_rect(F0 &&f, const T1 f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::ISZ>(i.v())) {
      const auto &[d_a0, d_a1] = std::get<typename instruction::ISZ>(i.v());
      return f(d_a0, d_a1);
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 instruction_rec(F0 &&f, const T1 f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::ISZ>(i.v())) {
      const auto &[d_a0, d_a1] = std::get<typename instruction::ISZ>(i.v());
      return f(d_a0, d_a1);
    } else {
      return f0;
    }
  }

  __attribute__((pure)) static instruction
  count_loop_test(unsigned int loop_addr);
  __attribute__((pure)) static unsigned int target_of(const instruction &i);
  static inline const unsigned int t = target_of(count_loop_test(37u));
};

#endif // INCLUDED_COUNT_LOOP_TEST_TARGET
