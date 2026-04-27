#ifndef INCLUDED_MODULE_TYPE_NAME_CLASH_PROBE
#define INCLUDED_MODULE_TYPE_NAME_CLASH_PROBE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct ModuleTypeNameClashProbe {
  struct M_Mod {
    struct t {
      // TYPES
      struct T0 {
        Bool0 d_a0;
      };

      using variant_t = std::variant<T0>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      t() {}

      explicit t(T0 _v) : d_v_(std::move(_v)) {}

      t(const t &_other) : d_v_(std::move(_other.clone().d_v_)) {}

      t(t &&_other) : d_v_(std::move(_other.d_v_)) {}

      __attribute__((pure)) t &operator=(const t &_other) {
        d_v_ = std::move(_other.clone().d_v_);
        return *this;
      }

      __attribute__((pure)) t &operator=(t &&_other) {
        d_v_ = std::move(_other.d_v_);
        return *this;
      }

      // ACCESSORS
      __attribute__((pure)) t clone() const {
        auto &&_sv = *(this);
        const auto &[d_a0] = std::get<T0>(_sv.v());
        return t(T0{d_a0});
      }

      // CREATORS
      constexpr static t t0(Bool0 a0) { return t(T0{std::move(a0)}); }

      // MANIPULATORS
      __attribute__((pure)) variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      __attribute__((pure)) t *operator->() { return this; }

      __attribute__((pure)) const t *operator->() const { return this; }

      __attribute__((pure)) bool operator!=(std::nullptr_t) const {
        return true;
      }

      __attribute__((pure)) bool operator==(std::nullptr_t) const {
        return false;
      }

      // MANIPULATORS
      void reset() { *this = t(); }

      // ACCESSORS
      __attribute__((pure)) const variant_t &v() const { return d_v_; }
    };

    template <typename T1, MapsTo<T1, Bool0> F0>
    static T1 t_rect(F0 &&f, const t &t0) {
      const auto &[d_a0] = std::get<typename t::T0>(t0.v());
      return f(d_a0);
    }

    template <typename T1, MapsTo<T1, Bool0> F0>
    static T1 t_rec(F0 &&f, const t &t0) {
      const auto &[d_a0] = std::get<typename t::T0>(t0.v());
      return f(d_a0);
    }
  };

  struct M {
    // TYPES
    struct MkM {
      Bool0 d_a0;
    };

    using variant_t = std::variant<MkM>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    M() {}

    explicit M(MkM _v) : d_v_(std::move(_v)) {}

    M(const M &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    M(M &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) M &operator=(const M &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) M &operator=(M &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) M clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<MkM>(_sv.v());
      return M(MkM{d_a0});
    }

    // CREATORS
    constexpr static M mkm(Bool0 a0) { return M(MkM{std::move(a0)}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) M *operator->() { return this; }

    __attribute__((pure)) const M *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = M(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, Bool0> F0>
  static T1 M_rect(F0 &&f, const M &m) {
    const auto &[d_a0] = std::get<typename M::MkM>(m.v());
    return f(d_a0);
  }

  template <typename T1, MapsTo<T1, Bool0> F0>
  static T1 M_rec(F0 &&f, const M &m) {
    const auto &[d_a0] = std::get<typename M::MkM>(m.v());
    return f(d_a0);
  }

  static inline const Bool0 sample = Bool0::e_TRUE0;
};

#endif // INCLUDED_MODULE_TYPE_NAME_CLASH_PROBE
