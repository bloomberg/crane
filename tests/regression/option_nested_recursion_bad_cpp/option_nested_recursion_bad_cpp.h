#ifndef INCLUDED_OPTION_NESTED_RECURSION_BAD_CPP
#define INCLUDED_OPTION_NESTED_RECURSION_BAD_CPP

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

struct OptionNestedRecursionBadCpp {
  /// chain's recursive occurrence is nested under option, which
  /// "Mapping/Std.v" maps to std::optional. The field is stored behind a
  /// shared_ptr, so its C++ type is
  /// std::shared_ptr<std::optional<chain>>, but the generated match on the
  /// option forgets to dereference the pointer before probing the optional:
  /// it emits o.has_value() against the shared_ptr rather than
  /// dereferencing it first. The result does not compile:
  ///
  /// error: no member named 'has_value' in
  /// 'std::shared_ptr<std::optional<...::chain>>'
  ///
  /// A one-constructor wrapper is enough; nothing here depends on option
  /// specifically beyond its being a mapped type.
  struct chain {
    // TYPES
    struct Link {
      uint64_t a0;
      std::shared_ptr<std::optional<chain>> a1;
    };

    using variant_t = std::variant<Link>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Link _v) : v_(std::move(_v)) {}

    static chain link(uint64_t a0, std::optional<chain> a1) {
      return chain(
          Link{a0, std::make_shared<std::optional<chain>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, std::optional<chain> &>
  static T1 chain_rect(F0 &&f, const chain &c) {
    const auto &[a0, a1] = std::get<typename chain::Link>(c.v());
    return f(a0, *a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, std::optional<chain> &>
  static T1 chain_rec(F0 &&f, const chain &c) {
    const auto &[a0, a1] = std::get<typename chain::Link>(c.v());
    return f(a0, *a1);
  }

  static chain build(uint64_t n);
  static uint64_t depth(const chain &c);
  static uint64_t run(uint64_t n);
};

#endif // INCLUDED_OPTION_NESTED_RECURSION_BAD_CPP
