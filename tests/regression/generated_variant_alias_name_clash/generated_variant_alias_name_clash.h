#ifndef INCLUDED_GENERATED_VARIANT_ALIAS_NAME_CLASH
#define INCLUDED_GENERATED_VARIANT_ALIAS_NAME_CLASH

#include <type_traits>
#include <utility>
#include <variant>

struct GeneratedVariantAliasNameClash {
  /// Generated ADT classes contain an internal alias named variant_t for the
  /// backing std::variant.  If the Rocq inductive itself is named variant_t,
  /// Crane generates a C++ class variant_t that also declares
  /// using variant_t = ... inside the class.  C++ rejects this because the
  /// nested type alias has the same name as the enclosing class.
  struct variant_t {
    // TYPES
    struct Empty {};

    struct Flag {
      bool a0;
    };

    using variant_t_ = std::variant<Empty, Flag>;

  private:
    // DATA
    variant_t_ v_;

  public:
    // CREATORS
    variant_t() {}

    explicit variant_t(Empty _v) : v_(_v) {}

    explicit variant_t(Flag _v) : v_(std::move(_v)) {}

    variant_t(const variant_t &_other) : v_(std::move(_other.clone().v_)) {}

    variant_t(variant_t &&_other) noexcept : v_(std::move(_other.v_)) {}

    variant_t &operator=(const variant_t &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    variant_t &operator=(variant_t &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    variant_t clone() const {
      if (std::holds_alternative<Empty>(this->v())) {
        return variant_t(Empty{});
      } else {
        const auto &[a0] = std::get<Flag>(this->v());
        return variant_t(Flag{a0});
      }
    }

    // CREATORS
    static variant_t empty() { return variant_t(Empty{}); }

    static variant_t flag(bool a0) { return variant_t(Flag{a0}); }

    // MANIPULATORS
    inline variant_t_ &v_mut() { return v_; }

    // ACCESSORS
    const variant_t_ &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, bool &>
  static T1 variant_t_rect(T1 f, F1 &&f0, const variant_t &v) {
    if (std::holds_alternative<typename variant_t::Empty>(v.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename variant_t::Flag>(v.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, bool &>
  static T1 variant_t_rec(T1 f, F1 &&f0, const variant_t &v) {
    if (std::holds_alternative<typename variant_t::Empty>(v.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename variant_t::Flag>(v.v());
      return f0(a0);
    }
  }

  static bool is_flag(const variant_t &x);
  static inline const bool sample = is_flag(variant_t::flag(true));
};

#endif // INCLUDED_GENERATED_VARIANT_ALIAS_NAME_CLASH
