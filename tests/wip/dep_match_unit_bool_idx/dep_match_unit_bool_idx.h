#ifndef INCLUDED_DEP_MATCH_UNIT_BOOL_IDX
#define INCLUDED_DEP_MATCH_UNIT_BOOL_IDX

#include <type_traits>
#include <utility>
#include <variant>

struct DepMatchUnitBoolIdx {
  struct tagged {
    // TYPES
    struct TA {
      uint64_t a0;
    };

    struct TB {
      bool a0;
    };

    using variant_t = std::variant<TA, TB>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tagged() {}

    explicit tagged(TA _v) : v_(std::move(_v)) {}

    explicit tagged(TB _v) : v_(std::move(_v)) {}

    static tagged ta(uint64_t a0) { return tagged(TA{a0}); }

    static tagged tb(bool a0) { return tagged(TB{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, bool &>
  static T1 tagged_rect(F0 &&f, F1 &&f0, bool, const tagged &t) {
    if (std::holds_alternative<typename tagged::TA>(t.v())) {
      const auto &[a0] = std::get<typename tagged::TA>(t.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename tagged::TB>(t.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, bool &>
  static T1 tagged_rec(F0 &&f, F1 &&f0, bool, const tagged &t) {
    if (std::holds_alternative<typename tagged::TA>(t.v())) {
      const auto &[a0] = std::get<typename tagged::TA>(t.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename tagged::TB>(t.v());
      return f0(a0);
    }
  }

  static uint64_t get(const tagged &t);
  static inline const uint64_t go = get(tagged::ta(UINT64_C(5)));
};

#endif // INCLUDED_DEP_MATCH_UNIT_BOOL_IDX
