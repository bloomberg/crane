#ifndef INCLUDED_VALUE_TYPE_MATCH_FIX
#define INCLUDED_VALUE_TYPE_MATCH_FIX

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct ValueTypeMatchFix {
  /// A non-recursive inductive (will be a value type).
  struct triple {
    // TYPES
    struct MkTriple {
      unsigned int d_a0;
      unsigned int d_a1;
      unsigned int d_a2;
    };

    using variant_t = std::variant<MkTriple>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit triple(MkTriple _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<triple> mktriple(unsigned int a0, unsigned int a1,
                                            unsigned int a2) {
      return std::make_shared<triple>(
          MkTriple{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1,
            MapsTo<T1, unsigned int, unsigned int, unsigned int> F0>
  static T1 triple_rect(F0 &&f, const std::shared_ptr<triple> &t) {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename triple::MkTriple>(t->v());
    return f(d_a0, d_a1, d_a2);
  }

  template <typename T1,
            MapsTo<T1, unsigned int, unsigned int, unsigned int> F0>
  static T1 triple_rec(F0 &&f, const std::shared_ptr<triple> &t) {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename triple::MkTriple>(t->v());
    return f(d_a0, d_a1, d_a2);
  }

  /// A fixpoint that captures a field from a value-type match.
  ///
  /// BUG HYPOTHESIS: triple is a value type (stack-allocated, non-recursive).
  /// When pattern matching on a value type, the fields are bound as
  /// references into the stack-allocated object. If a fixpoint captures
  /// these references by & and then escapes, the references dangle
  /// when the function returns and the value type is destroyed.
  ///
  /// This is different from pointer-based (shared_ptr) types where the
  /// field data lives on the heap and persists as long as the shared_ptr.
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  make_adder_from_triple(const std::shared_ptr<triple> &t);
  /// test1: MkTriple 10 20 30 -> base=60, go(5) = 60+5 = 65.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = make_adder_from_triple(triple::mktriple(10u, 20u, 30u));
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(5u);
    } else {
      return 999u;
    }
  }();
  /// test2: With noise between creation and use.
  static inline const unsigned int test2 = []() {
    std::optional<std::function<unsigned int(unsigned int)>> o =
        make_adder_from_triple(triple::mktriple(100u, 200u, 300u));
    unsigned int noise = (42u + 13u);
    if (o.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *o;
      return (f(0u) + noise);
    } else {
      return 999u;
    }
  }();
  /// Direct capture of pattern fields (no intermediate let binding).
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  make_field_adder(const std::shared_ptr<triple> &t);
  /// test3: MkTriple 42 0 0 -> a=42, go(3) = 42+3 = 45.
  static inline const unsigned int test3 = []() -> unsigned int {
    auto _cs = make_field_adder(triple::mktriple(42u, 0u, 0u));
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(3u);
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_VALUE_TYPE_MATCH_FIX
