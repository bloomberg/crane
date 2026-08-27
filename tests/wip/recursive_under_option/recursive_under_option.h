#ifndef INCLUDED_RECURSIVE_UNDER_OPTION
#define INCLUDED_RECURSIVE_UNDER_OPTION

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// WIP: A constructor field holding the inductive under an `option`
/// (`N : option c -> c`) is stored as `shared_ptr<optional<c>>` but the
/// generated pattern match calls `.has_value()` on the pointer.
struct RecursiveUnderOption {
  struct c {
    // TYPES
    struct N {
      std::shared_ptr<std::optional<c>> a0;
    };

    using variant_t = std::variant<N>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    c() {}

    explicit c(N _v) : v_(std::move(_v)) {}

    static c n(std::optional<c> a0) {
      return c(N{std::make_shared<std::optional<c>>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, std::optional<c> &>
  static T1 c_rect(F0 &&f, const c &c0) {
    const auto &[a0] = std::get<typename c::N>(c0.v());
    return f(*a0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, std::optional<c> &>
  static T1 c_rec(F0 &&f, const c &c0) {
    const auto &[a0] = std::get<typename c::N>(c0.v());
    return f(*a0);
  }

  static c build(uint64_t n);
  static uint64_t depth(const c &x);
  static inline const uint64_t go = depth(build(UINT64_C(1000)));
};

#endif // INCLUDED_RECURSIVE_UNDER_OPTION
