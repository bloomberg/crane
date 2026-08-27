#ifndef INCLUDED_RECURSIVE_UNDER_PAIR
#define INCLUDED_RECURSIVE_UNDER_PAIR

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// WIP: A constructor field holding the inductive under a pair
/// (`N : (nat * c) -> c`) is stored as `shared_ptr<pair<uint64_t, c>>` but the
/// generated code reads `.second` off the pointer.
struct RecursiveUnderPair {
  struct c {
    // TYPES
    struct Stop {};

    struct N {
      std::shared_ptr<std::pair<uint64_t, c>> a0;
    };

    using variant_t = std::variant<Stop, N>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    c() {}

    explicit c(Stop _v) : v_(_v) {}

    explicit c(N _v) : v_(std::move(_v)) {}

    static c stop() { return c(Stop{}); }

    static c n(std::pair<uint64_t, c> a0) {
      return c(N{std::make_shared<std::pair<uint64_t, c>>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, std::pair<uint64_t, c> &>
  static T1 c_rect(T1 f, F1 &&f0, const c &c0) {
    if (std::holds_alternative<typename c::Stop>(c0.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename c::N>(c0.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, std::pair<uint64_t, c> &>
  static T1 c_rec(T1 f, F1 &&f0, const c &c0) {
    if (std::holds_alternative<typename c::Stop>(c0.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename c::N>(c0.v());
      return f0(*a0);
    }
  }

  static c build(uint64_t n);
  static uint64_t depth(const c &x);
  static inline const uint64_t go = depth(build(UINT64_C(1000)));
};

#endif // INCLUDED_RECURSIVE_UNDER_PAIR
