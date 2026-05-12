#ifndef INCLUDED_GENERATED_VARIANT_FACTORY_NAME_CLASH
#define INCLUDED_GENERATED_VARIANT_FACTORY_NAME_CLASH

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

struct GeneratedVariantFactoryNameClash {
  /// Constructors become static factory methods on the generated C++ class.  A
  /// constructor named Variant_t lowers to a factory named variant_t, which
  /// collides with Crane's internal using variant_t = ... alias for the backing
  /// std::variant.  The generated C++ does not compile because a member type
  /// alias and a static member function cannot share this name cleanly.
  struct token {
    // TYPES
    struct Variant_t {};

    struct Other {
      bool d_a0;
    };

    using variant_t = std::variant<Variant_t, Other>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    token() {}

    explicit token(Variant_t _v) : d_v_(_v) {}

    explicit token(Other _v) : d_v_(std::move(_v)) {}

    token(const token &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    token(token &&_other) : d_v_(std::move(_other.d_v_)) {}

    token &operator=(const token &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    token &operator=(token &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    token clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Variant_t>(_sv.v())) {
        return token(Variant_t());
      } else {
        const auto &[d_a0] = std::get<Other>(_sv.v());
        return token(Other(d_a0));
      }
    }

    // CREATORS
    static token Variant_t_() { return token(Variant_t()); }

    static token other(bool a0) { return token(Other(std::move(a0))); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, bool &>
  static T1 token_rect(const T1 f, F1 &&f0, const token &t) {
    if (std::holds_alternative<typename token::Variant_t>(t.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename token::Other>(t.v());
      return f0(d_a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, bool &>
  static T1 token_rec(const T1 f, F1 &&f0, const token &t) {
    if (std::holds_alternative<typename token::Variant_t>(t.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename token::Other>(t.v());
      return f0(d_a0);
    }
  }

  static bool is_variant(const token &t);
  static inline const bool sample = is_variant(token::Variant_t_());
};

#endif // INCLUDED_GENERATED_VARIANT_FACTORY_NAME_CLASH
