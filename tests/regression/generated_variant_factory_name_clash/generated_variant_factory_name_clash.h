#ifndef INCLUDED_GENERATED_VARIANT_FACTORY_NAME_CLASH
#define INCLUDED_GENERATED_VARIANT_FACTORY_NAME_CLASH

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
      bool a0;
    };

    using variant_t = std::variant<Variant_t, Other>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    token() {}

    explicit token(Variant_t _v) : v_(_v) {}

    explicit token(Other _v) : v_(std::move(_v)) {}

    static token Variant_t_() { return token(Variant_t{}); }

    static token other(bool a0) { return token(Other{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, bool &>
  static T1 token_rect(T1 f, F1 &&f0, const token &t) {
    if (std::holds_alternative<typename token::Variant_t>(t.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename token::Other>(t.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, bool &>
  static T1 token_rec(T1 f, F1 &&f0, const token &t) {
    if (std::holds_alternative<typename token::Variant_t>(t.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename token::Other>(t.v());
      return f0(a0);
    }
  }

  static bool is_variant(const token &t);
  static inline const bool sample = is_variant(token::Variant_t_());
};

#endif // INCLUDED_GENERATED_VARIANT_FACTORY_NAME_CLASH
