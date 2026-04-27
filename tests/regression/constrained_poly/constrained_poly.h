#ifndef INCLUDED_CONSTRAINED_POLY
#define INCLUDED_CONSTRAINED_POLY

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ConstrainedPoly {
  template <typename T1> static T1 poly_id(const T1 x) { return x; }

  template <typename t_A, typename t_B> struct UPair {
    t_A ufst;
    t_B usnd;

    __attribute__((pure)) UPair<t_A, t_B> *operator->() { return this; }

    __attribute__((pure)) const UPair<t_A, t_B> *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) UPair<t_A, t_B> clone() const {
      return UPair<t_A, t_B>{
          [](auto &&__v) -> t_A {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).ufst),
          [](auto &&__v) -> t_B {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).usnd)};
    }
  };

  template <typename T1, typename T2>
  constexpr static UPair<T2, T1> swap(const UPair<T1, T2> &p) {
    return UPair<T2, T1>{p.usnd, p.ufst};
  }

  template <typename T1, typename T2>
  __attribute__((pure)) static UPair<T1, T2> wrap_pair(const T1 a, const T2 b) {
    return UPair<T1, T2>{a, b};
  }

  template <typename t_A> struct UOption {
    // TYPES
    struct USome {
      t_A d_a0;
    };

    struct UNone {};

    using variant_t = std::variant<USome, UNone>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    UOption() {}

    explicit UOption(USome _v) : d_v_(std::move(_v)) {}

    explicit UOption(UNone _v) : d_v_(_v) {}

    UOption(const UOption<t_A> &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    UOption(UOption<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) UOption<t_A> &operator=(const UOption<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) UOption<t_A> &operator=(UOption<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) UOption<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<USome>(_sv.v())) {
        const auto &[d_a0] = std::get<USome>(_sv.v());
        t_A __c0;
        if constexpr (
            requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
            requires { d_a0->clone(); } && requires { d_a0.get(); }) {
          using _E = std::remove_cvref_t<decltype(*d_a0)>;
          __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
        } else if constexpr (requires { d_a0.clone(); }) {
          __c0 = d_a0.clone();
        } else {
          __c0 = d_a0;
        }
        return UOption<t_A>(USome{std::move(__c0)});
      } else {
        return UOption<t_A>(UNone{});
      }
    }

    // CREATORS
    template <typename _U> explicit UOption(const UOption<_U> &_other) {
      if (std::holds_alternative<typename UOption<_U>::USome>(_other.v())) {
        const auto &[d_a0] = std::get<typename UOption<_U>::USome>(_other.v());
        d_v_ = USome{[&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
          if constexpr (
              requires { *__v; } && !requires { std::declval<_DstT>().get(); })
            return _DstT(*__v);
          else if constexpr (
              !requires { *__v; } &&
              requires { std::declval<_DstT>().get(); }) {
            using _E =
                std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
            return std::make_unique<_E>(std::move(__v));
          } else
            return _DstT(__v);
        }(d_a0)};
      } else {
        d_v_ = UNone{};
      }
    }

    __attribute__((pure)) static UOption<t_A> usome(t_A a0) {
      return UOption(USome{std::move(a0)});
    }

    constexpr static UOption<t_A> unone() { return UOption(UNone{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) UOption<t_A> *operator->() { return this; }

    __attribute__((pure)) const UOption<t_A> *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = UOption<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 UOption_rect(F0 &&f, const T2 f0, const UOption<T1> &u) {
    if (std::holds_alternative<typename UOption<T1>::USome>(u.v())) {
      const auto &[d_a0] = std::get<typename UOption<T1>::USome>(u.v());
      return f(d_a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 UOption_rec(F0 &&f, const T2 f0, const UOption<T1> &u) {
    if (std::holds_alternative<typename UOption<T1>::USome>(u.v())) {
      const auto &[d_a0] = std::get<typename UOption<T1>::USome>(u.v());
      return f(d_a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static UOption<T2> uoption_map(F0 &&f,
                                                       const UOption<T1> &o) {
    if (std::holds_alternative<typename UOption<T1>::USome>(o.v())) {
      const auto &[d_a0] = std::get<typename UOption<T1>::USome>(o.v());
      return UOption<T2>::usome(f(d_a0));
    } else {
      return UOption<T2>::unone();
    }
  }

  static inline const unsigned int test_id_nat = poly_id<unsigned int>(42u);
  static inline const bool test_id_bool = poly_id<bool>(true);
  static inline const UPair<unsigned int, bool> test_pair =
      wrap_pair<unsigned int, bool>(5u, false);
  static inline const UPair<bool, unsigned int> test_swap =
      swap<unsigned int, bool>(test_pair);
  static inline const unsigned int test_fst = test_pair.ufst;
  static inline const bool test_snd = test_pair.usnd;
  static inline const UOption<unsigned int> test_umap =
      uoption_map<unsigned int, unsigned int>(
          [](const unsigned int &n) { return (n + 1u); },
          UOption<unsigned int>::usome(9u));
};

#endif // INCLUDED_CONSTRAINED_POLY
