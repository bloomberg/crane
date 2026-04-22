#ifndef INCLUDED_MODULE_TYPE_NAME_CLASH_PROBE
#define INCLUDED_MODULE_TYPE_NAME_CLASH_PROBE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
      explicit t(T0 _v) : d_v_(std::move(_v)) {}

      static std::shared_ptr<t> t0(Bool0 a0) {
        return std::make_shared<t>(T0{std::move(a0)});
      }

      // MANIPULATORS
      __attribute__((pure)) variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      __attribute__((pure)) const variant_t &v() const { return d_v_; }
    };

    template <typename T1, MapsTo<T1, Bool0> F0>
    static T1 t_rect(F0 &&f, const std::shared_ptr<t> &t0) {
      const auto &[d_a0] = std::get<typename t::T0>(t0->v());
      return f(d_a0);
    }

    template <typename T1, MapsTo<T1, Bool0> F0>
    static T1 t_rec(F0 &&f, const std::shared_ptr<t> &t0) {
      const auto &[d_a0] = std::get<typename t::T0>(t0->v());
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
    explicit M(MkM _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<M> mkm(Bool0 a0) {
      return std::make_shared<M>(MkM{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, Bool0> F0>
  static T1 M_rect(F0 &&f, const std::shared_ptr<M> &m) {
    const auto &[d_a0] = std::get<typename M::MkM>(m->v());
    return f(d_a0);
  }

  template <typename T1, MapsTo<T1, Bool0> F0>
  static T1 M_rec(F0 &&f, const std::shared_ptr<M> &m) {
    const auto &[d_a0] = std::get<typename M::MkM>(m->v());
    return f(d_a0);
  }

  static inline const Bool0 sample = Bool0::e_TRUE0;
};

#endif // INCLUDED_MODULE_TYPE_NAME_CLASH_PROBE
