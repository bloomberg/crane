#ifndef INCLUDED_FACTORY_HIDES_FIELD_TYPE
#define INCLUDED_FACTORY_HIDES_FIELD_TYPE

#include <atomic>
#include <cstdint>
#include <type_traits>
#include <utility>
#include <variant>

struct FactoryHidesFieldType {
  struct pt {
    uint64_t px;
    uint64_t py;
  };

  struct shape {
    // TYPES
    struct Pt {
      pt a0;
    };

    struct Tag {
      pt a0;
    };

    using variant_t = std::variant<Pt, Tag>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    shape() {}

    explicit shape(Pt _v) : v_(std::move(_v)) {}

    explicit shape(Tag _v) : v_(std::move(_v)) {}

    static shape pt(pt a0) { return shape(Pt{std::move(a0)}); }

    static shape tag(pt a0) { return shape(Tag{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const pt &> &&
             std::is_invocable_r_v<T1, F1 &, const pt &>
  static T1 shape_rect(F0 &&f, F1 &&f0, const shape &s) {
    if (std::holds_alternative<typename shape::Pt>(s.v())) {
      const auto &[a0] = std::get<typename shape::Pt>(s.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename shape::Tag>(s.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
  static T1 shape_rec(F0 &&f, F1 &&f0, const shape &s) {
    return shape_rect<T1>(f, f0, s);
  }

  static uint64_t area(const shape &s);
  static inline const uint64_t result =
      (area(shape::tag(pt{UINT64_C(2), UINT64_C(3)})) +
       area(shape::pt(pt{UINT64_C(2), UINT64_C(3)})));
};

#endif // INCLUDED_FACTORY_HIDES_FIELD_TYPE
