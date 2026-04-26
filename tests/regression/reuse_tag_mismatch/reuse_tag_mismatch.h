#ifndef INCLUDED_REUSE_TAG_MISMATCH
#define INCLUDED_REUSE_TAG_MISMATCH

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

struct ReuseTagMismatch {
  /// BUG HYPOTHESIS: The reuse optimization mutates variant fields in-place
  /// when use_count() == 1 and the tail constructor has the same arity
  /// as the matched constructor, even when they are DIFFERENT constructors.
  /// This leaves the variant with the WRONG tag — the original matched
  /// constructor tag persists instead of changing to the tail constructor.
  ///
  /// The reuse optimization fires when:
  /// 1. The scrutinee is "owned" (escapes in some code path)
  /// 2. The tail constructor has the same arity as the matched constructor
  /// 3. same_inductive holds (same type)
  /// 4. use_count() == 1 at runtime
  ///
  /// It does NOT check that matched_ctor == tail_ctor.
  struct direction {
    // TYPES
    struct GoUp {
      unsigned int d_a0;
    };

    struct GoDown {
      unsigned int d_a0;
    };

    using variant_t = std::variant<GoUp, GoDown>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    direction() {}

    explicit direction(GoUp _v) : d_v_(std::move(_v)) {}

    explicit direction(GoDown _v) : d_v_(std::move(_v)) {}

    direction(const direction &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    direction(direction &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) direction &operator=(const direction &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) direction &operator=(direction &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) direction clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<GoUp>(_sv.v())) {
        const auto &[d_a0] = std::get<GoUp>(_sv.v());
        return direction(GoUp{d_a0});
      } else {
        const auto &[d_a0] = std::get<GoDown>(_sv.v());
        return direction(GoDown{d_a0});
      }
    }

    // CREATORS
    __attribute__((pure)) static direction goup(unsigned int a0) {
      return direction(GoUp{std::move(a0)});
    }

    __attribute__((pure)) static direction godown(unsigned int a0) {
      return direction(GoDown{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) direction *operator->() { return this; }

    __attribute__((pure)) const direction *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = direction(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 direction_rect(F0 &&f, F1 &&f0, const direction &d) {
    if (std::holds_alternative<typename direction::GoUp>(d.v())) {
      const auto &[d_a0] = std::get<typename direction::GoUp>(d.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename direction::GoDown>(d.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 direction_rec(F0 &&f, F1 &&f0, const direction &d) {
    if (std::holds_alternative<typename direction::GoUp>(d.v())) {
      const auto &[d_a0] = std::get<typename direction::GoUp>(d.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename direction::GoDown>(d.v());
      return f0(d_a0);
    }
  }

  /// The 'else d' branch causes d to escape (returned in tail position).
  /// This makes d "owned" (infer_owned_params marks it).
  /// The 'then' branch's match has reuse candidates because:
  /// - GoUp/GoDown are the same inductive (direction)
  /// - Both have arity 1
  /// But GoUp and GoDown are DIFFERENT constructors.
  __attribute__((pure)) static direction id_or_flip(direction d,
                                                    const bool &flip_flag);
  /// test1: flip GoUp 42 -> should be GoDown 42.
  /// Match on the result:
  /// - GoUp _ => 1 (wrong, reuse bug would make this match)
  /// - GoDown _ => 2 (correct)
  static inline const unsigned int test1 = []() {
    auto &&_sv = id_or_flip(direction::goup(42u), true);
    if (std::holds_alternative<typename direction::GoUp>(_sv.v())) {
      return 1u;
    } else {
      return 2u;
    }
  }();
  /// test2: no flip -> should be GoUp 42 unchanged.
  static inline const unsigned int test2 = []() {
    auto &&_sv = id_or_flip(direction::goup(42u), false);
    if (std::holds_alternative<typename direction::GoUp>(_sv.v())) {
      return 1u;
    } else {
      return 2u;
    }
  }();
  /// test3: flip GoDown 100 -> should be GoUp 100.
  static inline const unsigned int test3 = []() {
    auto &&_sv = id_or_flip(direction::godown(100u), true);
    if (std::holds_alternative<typename direction::GoUp>(_sv.v())) {
      return 3u;
    } else {
      return 4u;
    }
  }();
  /// test4: use the flipped value's payload.
  static inline const unsigned int test4 = []() {
    auto &&_sv3 = id_or_flip(direction::goup(10u), true);
    if (std::holds_alternative<typename direction::GoUp>(_sv3.v())) {
      const auto &[d_a03] = std::get<typename direction::GoUp>(_sv3.v());
      return (d_a03 + 1000u);
    } else {
      const auto &[d_a03] = std::get<typename direction::GoDown>(_sv3.v());
      return d_a03;
    }
  }();
};

#endif // INCLUDED_REUSE_TAG_MISMATCH
