#ifndef INCLUDED_DEP_MATCH_UNIT_OPTION
#define INCLUDED_DEP_MATCH_UNIT_OPTION

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

struct DepMatchUnitOption {
  struct tg {
    // TYPES
    struct TO {
      std::optional<uint64_t> a0;
    };

    struct TU {};

    using variant_t = std::variant<TO, TU>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tg() {}

    explicit tg(TO _v) : v_(std::move(_v)) {}

    explicit tg(TU _v) : v_(_v) {}

    static tg to(std::optional<uint64_t> a0) { return tg(TO{std::move(a0)}); }

    static tg tu() { return tg(TU{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, std::optional<uint64_t> &>
  static T1 tg_rect(F0 &&f, T1 f0, bool, const tg &t) {
    if (std::holds_alternative<typename tg::TO>(t.v())) {
      const auto &[a0] = std::get<typename tg::TO>(t.v());
      return f(a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, std::optional<uint64_t> &>
  static T1 tg_rec(F0 &&f, T1 f0, bool, const tg &t) {
    if (std::holds_alternative<typename tg::TO>(t.v())) {
      const auto &[a0] = std::get<typename tg::TO>(t.v());
      return f(a0);
    } else {
      return f0;
    }
  }

  static std::optional<uint64_t> get(const tg &t);
  static inline const uint64_t go = []() -> uint64_t {
    auto _cs = get(tg::to(std::make_optional<uint64_t>(UINT64_C(4))));
    if (_cs.has_value()) {
      const uint64_t &n = *_cs;
      return n;
    } else {
      return UINT64_C(0);
    }
  }();
};

#endif // INCLUDED_DEP_MATCH_UNIT_OPTION
