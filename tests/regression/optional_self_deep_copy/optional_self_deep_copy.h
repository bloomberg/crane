#ifndef INCLUDED_OPTIONAL_SELF_DEEP_COPY
#define INCLUDED_OPTIONAL_SELF_DEEP_COPY

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

struct OptionalSelfDeepCopy {
  /// Self-recursion hidden under option is not the direct field shape handled
  /// by the iterative clone/destructor generator.  Crane currently lowers the
  /// field to an owned std::optional containing an owned chain, then emits
  /// invalid clone code that tries to call .clone() on the std::optional
  /// object itself.  The generated C++ does not compile.
  struct chain {
    // TYPES
    struct Stop {};

    struct More {
      std::shared_ptr<std::optional<std::shared_ptr<chain>>> a0;
    };

    using variant_t = std::variant<Stop, More>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Stop _v) : v_(_v) {}

    explicit chain(More _v) : v_(std::move(_v)) {}

    static chain stop() { return chain(Stop{}); }

    static chain more(std::optional<std::shared_ptr<chain>> a0) {
      return chain(More{std::make_shared<std::optional<std::shared_ptr<chain>>>(
          std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, std::optional<chain> &>
  static T1 chain_rect(T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename chain::More>(c.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, std::optional<chain> &>
  static T1 chain_rec(T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename chain::More>(c.v());
      return f0(*a0);
    }
  }

  static std::pair<chain, chain> dup_chain(chain c);
};

#endif // INCLUDED_OPTIONAL_SELF_DEEP_COPY
