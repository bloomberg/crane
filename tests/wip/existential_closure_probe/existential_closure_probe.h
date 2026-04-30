#ifndef INCLUDED_EXISTENTIAL_CLOSURE_PROBE
#define INCLUDED_EXISTENTIAL_CLOSURE_PROBE

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ExistentialClosureProbe {
  /// Type-indexed inductive wrapping a value of erased type.
  /// The type index A is erased to std::any by Crane.
  /// Values stored in the wrapper must be recovered via any_cast.
  struct wrap {
    // TYPES
    struct Wrap0 {
      std::any d_a;
    };

    using variant_t = std::variant<Wrap0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    wrap() {}

    explicit wrap(Wrap0 _v) : d_v_(std::move(_v)) {}

    wrap(const wrap &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    wrap(wrap &&_other) : d_v_(std::move(_other.d_v_)) {}

    wrap &operator=(const wrap &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    wrap &operator=(wrap &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    wrap clone() const {
      auto &&_sv = *(this);
      const auto &[d_a] = std::get<Wrap0>(_sv.v());
      return wrap(Wrap0{d_a});
    }

    // CREATORS
    static wrap wrap0(std::any a) { return wrap(Wrap0{std::move(a)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F0>
  static T1 wrap_rect(F0 &&f, const wrap &w) {
    const auto &[d_a] = std::get<typename wrap::Wrap0>(w.v());
    return std::any_cast<T1>(f(d_a));
  }

  template <typename T1, typename F0>
  static T1 wrap_rec(F0 &&f, const wrap &w) {
    const auto &[d_a] = std::get<typename wrap::Wrap0>(w.v());
    return std::any_cast<T1>(f(d_a));
  }

  template <typename T1> static T1 unwrap(const wrap &w) {
    const auto &[d_a] = std::get<typename wrap::Wrap0>(w.v());
    return std::any_cast<T1>(d_a);
  }

  /// Pack a closure into a type-erased wrapper.
  static wrap pack_fn(unsigned int base);
  /// Unpack and apply.
  static unsigned int apply_packed(const wrap &_x0, const unsigned int &_x1);
  /// test1: pack base=10, apply to 5. Expected: 15.
  static inline const unsigned int test1 = apply_packed(pack_fn(10u), 5u);
  /// test2: Pack and unpack through a let binding.
  /// base=42, apply to 0. Expected: 42.
  static inline const unsigned int test2 = []() {
    wrap p = pack_fn(42u);
    return apply_packed(std::move(p), 0u);
  }();
  /// Store a closure that captures another closure.
  static wrap pack_composed(unsigned int a, unsigned int b);
  /// test3: a=3, b=2, g(5) = (5+3)*2 = 16.
  static inline const unsigned int test3 =
      apply_packed(pack_composed(3u, 2u), 5u);
};

#endif // INCLUDED_EXISTENTIAL_CLOSURE_PROBE
