#ifndef INCLUDED_DEP_MATCH_UNIT_FUN
#define INCLUDED_DEP_MATCH_UNIT_FUN

#include <functional>
#include <type_traits>
#include <utility>
#include <variant>

struct DepMatchUnitFun {
  struct tg {
    // TYPES
    struct TF {
      std::function<uint64_t(uint64_t)> a0;
    };

    struct TU {};

    using variant_t = std::variant<TF, TU>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tg() {}

    explicit tg(TF _v) : v_(std::move(_v)) {}

    explicit tg(TU _v) : v_(_v) {}

    static tg tf(std::function<uint64_t(uint64_t)> a0) {
      return tg(TF{std::move(a0)});
    }

    static tg tu() { return tg(TU{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &,
                                   std::function<uint64_t(uint64_t)> &>
  static T1 tg_rect(F0 &&f, T1 f0, bool, const tg &t) {
    if (std::holds_alternative<typename tg::TF>(t.v())) {
      const auto &[a0] = std::get<typename tg::TF>(t.v());
      return f(a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &,
                                   std::function<uint64_t(uint64_t)> &>
  static T1 tg_rec(F0 &&f, T1 f0, bool, const tg &t) {
    if (std::holds_alternative<typename tg::TF>(t.v())) {
      const auto &[a0] = std::get<typename tg::TF>(t.v());
      return f(a0);
    } else {
      return f0;
    }
  }

  static uint64_t get(const tg &t, uint64_t _x0);
  static inline const uint64_t go =
      get(tg::tf([](uint64_t x) { return (x + UINT64_C(1)); }), UINT64_C(4));
};

#endif // INCLUDED_DEP_MATCH_UNIT_FUN
