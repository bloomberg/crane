#ifndef INCLUDED_MODULE_TYPE_NAME_CLASH_PROBE
#define INCLUDED_MODULE_TYPE_NAME_CLASH_PROBE

#include <type_traits>
#include <utility>
#include <variant>

enum class Bool0 { TRUE_, FALSE_ };

struct ModuleTypeNameClashProbe {
  struct M_Mod {
    struct t {
      // TYPES
      struct T0 {
        Bool0 a0;
      };

      using variant_t = std::variant<T0>;

    private:
      // DATA
      variant_t v_;

    public:
      // CREATORS
      t() {}

      explicit t(T0 _v) : v_(std::move(_v)) {}

      t(const t &_other) : v_(std::move(_other.clone().v_)) {}

      t(t &&_other) : v_(std::move(_other.v_)) {}

      t &operator=(const t &_other) {
        v_ = std::move(_other.clone().v_);
        return *this;
      }

      t &operator=(t &&_other) {
        v_ = std::move(_other.v_);
        return *this;
      }

      // ACCESSORS
      t clone() const {
        const auto &[a0] = std::get<T0>(this->v());
        return t(T0{a0});
      }

      // CREATORS
      static t t0(Bool0 a0) { return t(T0{a0}); }

      // MANIPULATORS
      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }
    };

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, Bool0 &>
    static T1 t_rect(F0 &&f, const t &t0) {
      const auto &[a0] = std::get<typename t::T0>(t0.v());
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, Bool0 &>
    static T1 t_rec(F0 &&f, const t &t0) {
      const auto &[a0] = std::get<typename t::T0>(t0.v());
      return f(a0);
    }
  };

  struct M {
    // TYPES
    struct MkM {
      Bool0 a0;
    };

    using variant_t = std::variant<MkM>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    M() {}

    explicit M(MkM _v) : v_(std::move(_v)) {}

    M(const M &_other) : v_(std::move(_other.clone().v_)) {}

    M(M &&_other) : v_(std::move(_other.v_)) {}

    M &operator=(const M &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    M &operator=(M &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    M clone() const {
      const auto &[a0] = std::get<MkM>(this->v());
      return M(MkM{a0});
    }

    // CREATORS
    static M mkm(Bool0 a0) { return M(MkM{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, Bool0 &>
  static T1 M_rect(F0 &&f, const M &m) {
    const auto &[a0] = std::get<typename M::MkM>(m.v());
    return f(a0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, Bool0 &>
  static T1 M_rec(F0 &&f, const M &m) {
    const auto &[a0] = std::get<typename M::MkM>(m.v());
    return f(a0);
  }

  static inline const Bool0 sample = Bool0::TRUE_;
};

#endif // INCLUDED_MODULE_TYPE_NAME_CLASH_PROBE
