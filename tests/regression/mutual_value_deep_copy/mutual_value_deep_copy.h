#ifndef INCLUDED_MUTUAL_VALUE_DEEP_COPY
#define INCLUDED_MUTUAL_VALUE_DEEP_COPY

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MutualValueDeepCopy {
  /// Direct self-recursive value ADTs now get iterative clone/destruct paths.
  /// This test uses mutual recursion instead: a owns b, and b owns a.
  /// Crane currently generates recursive a::clone and b::clone methods that
  /// call each other through unique_ptr children.  Copying a deep alternating
  /// value with dup_a therefore overflows the C++ stack before the copied value
  /// can be used.
  struct a;
  struct b;

  struct a {
    // TYPES
    struct AEnd {};

    struct ANode {
      bool a0;
      std::shared_ptr<b> a1;
    };

    using variant_t = std::variant<AEnd, ANode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    a() {}

    explicit a(AEnd _v) : v_(_v) {}

    explicit a(ANode _v) : v_(std::move(_v)) {}

    static a aend() { return a(AEnd{}); }

    static a anode(bool a0, b a1) {
      return a(ANode{a0, std::make_shared<b>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct b {
    // TYPES
    struct BNode {
      std::shared_ptr<a> a0;
    };

    using variant_t = std::variant<BNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    b() {}

    explicit b(BNode _v) : v_(std::move(_v)) {}

    static b bnode(a a0) {
      return b(BNode{std::make_shared<a>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, bool &, b &>
  static T1 a_rect(T1 f, F1 &&f0, const a &a0) {
    if (std::holds_alternative<typename a::AEnd>(a0.v())) {
      return f;
    } else {
      const auto &[a1, a2] = std::get<typename a::ANode>(a0.v());
      return f0(a1, *a2);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, bool &, b &>
  static T1 a_rec(T1 f, F1 &&f0, const a &a0) {
    if (std::holds_alternative<typename a::AEnd>(a0.v())) {
      return f;
    } else {
      const auto &[a1, a2] = std::get<typename a::ANode>(a0.v());
      return f0(a1, *a2);
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, a &>
  static T1 b_rect(F0 &&f, const b &b0) {
    const auto &[a1] = std::get<typename b::BNode>(b0.v());
    return f(*a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, a &>
  static T1 b_rec(F0 &&f, const b &b0) {
    const auto &[a1] = std::get<typename b::BNode>(b0.v());
    return f(*a1);
  }

  static bool reaches_end_a(const a &x);
  static bool reaches_end_b(const b &y);
  static std::pair<a, a> dup_a(a x);
  static bool copied_reaches_end(const a &x);
};

#endif // INCLUDED_MUTUAL_VALUE_DEEP_COPY
