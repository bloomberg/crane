#ifndef INCLUDED_DEP_MATCH_UNIT_PAIR
#define INCLUDED_DEP_MATCH_UNIT_PAIR

#include <type_traits>
#include <utility>
#include <variant>

struct DepMatchUnitPair {
  struct tg {
    // TYPES
    struct TP {
      uint64_t a0;
      uint64_t a1;
    };

    struct TU {};

    using variant_t = std::variant<TP, TU>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tg() {}

    explicit tg(TP _v) : v_(std::move(_v)) {}

    explicit tg(TU _v) : v_(_v) {}

    static tg tp(uint64_t a0, uint64_t a1) { return tg(TP{a0, a1}); }

    static tg tu() { return tg(TU{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &>
  static T1 tg_rect(F0 &&f, T1 f0, bool, const tg &t) {
    if (std::holds_alternative<typename tg::TP>(t.v())) {
      const auto &[a0, a1] = std::get<typename tg::TP>(t.v());
      return f(a0, a1);
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &>
  static T1 tg_rec(F0 &&f, T1 f0, bool, const tg &t) {
    if (std::holds_alternative<typename tg::TP>(t.v())) {
      const auto &[a0, a1] = std::get<typename tg::TP>(t.v());
      return f(a0, a1);
    } else {
      return f0;
    }
  }

  static std::pair<uint64_t, uint64_t> get(const tg &t);
  static inline const uint64_t go =
      (get(tg::tp(UINT64_C(1), UINT64_C(2))).first +
       get(tg::tp(UINT64_C(1), UINT64_C(2))).second);
};

#endif // INCLUDED_DEP_MATCH_UNIT_PAIR
