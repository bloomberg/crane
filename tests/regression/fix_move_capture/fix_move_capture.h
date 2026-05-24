#ifndef INCLUDED_FIX_MOVE_CAPTURE
#define INCLUDED_FIX_MOVE_CAPTURE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct FixMoveCapture {
  /// BUG HYPOTHESIS: dead-after analysis vs fixpoint & capture.
  ///
  /// Crane's move tracking computes dead_in_a for let-bindings:
  /// a variable is "dead" after a let's RHS if it does not appear
  /// free in the continuation. It then generates std::move(var).
  ///
  /// But free_rels only tracks DIRECT de Bruijn references.
  /// If a fixpoint captures a variable by & and the variable is
  /// later consumed by a let-binding (via a function that takes it
  /// by value), free_rels sees no direct reference in the
  /// continuation — so the variable is moved.
  ///
  /// The fixpoint's & reference then points to a moved-from
  /// shared_ptr (null). Calling the fixpoint dereferences null.
  struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      uint64_t a0;
      std::shared_ptr<mylist> a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    static mylist mynil() { return mylist(Mynil{}); }

    static mylist mycons(uint64_t a0, mylist a1) {
      return mylist(Mycons{a0, std::make_shared<mylist>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, mylist &, T1 &>
  static T1 mylist_rect(T1 f0, F1 &&f1, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mynil>(m.v())) {
      return f0;
    } else {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f1(a0, *a1, mylist_rect<T1>(f0, f1, *a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, mylist &, T1 &>
  static T1 mylist_rec(T1 f0, F1 &&f1, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mynil>(m.v())) {
      return f0;
    } else {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f1(a0, *a1, mylist_rec<T1>(f0, f1, *a1));
    }
  }

  static uint64_t length(const mylist &l);
  static uint64_t sum(const mylist &l);
  /// dup_head stores l in the constructor → l escapes → owned.
  /// This means the caller passes l by value (move semantics).
  static mylist dup_head(mylist l);
  /// f l: defines a local fixpoint go that captures l by &.
  /// Then let t := dup_head l in ...:
  /// - dup_head takes l by value (owned, because l escapes in its body)
  /// - Crane sees that l (dead_in_a) is not free in continuation g 3 + length t
  /// - Generates dup_head(std::move(l))
  /// - l is now null in caller scope
  /// - g(3) calls fixpoint, which accesses l via & → null → CRASH
  static uint64_t f(mylist l);
  static inline const uint64_t test1 = f(mylist::mycons(
      UINT64_C(10),
      mylist::mycons(UINT64_C(20),
                     mylist::mycons(UINT64_C(30), mylist::mynil()))));
  /// Even simpler: use the fixpoint, then pass l to a consuming
  /// function. The addition's evaluation order is unspecified in C++,
  /// so we use a let-binding to force the order.
  static uint64_t f2(mylist l);
  static inline const uint64_t test2 = f2(mylist::mycons(
      UINT64_C(5), mylist::mycons(UINT64_C(15), mylist::mynil())));
};

#endif // INCLUDED_FIX_MOVE_CAPTURE
