#ifndef INCLUDED_REUSE_SELF_CYCLE
#define INCLUDED_REUSE_SELF_CYCLE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct ReuseSelfCycle {
  /// mycons at index 0 so reuse fires on the mycons branch.
  struct mylist {
    // TYPES
    struct Mycons {
      uint64_t a0;
      std::shared_ptr<mylist> a1;
    };

    struct Mynil {};

    using variant_t = std::variant<Mycons, Mynil>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    explicit mylist(Mynil _v) : v_(_v) {}

    static mylist mycons(uint64_t a0, mylist a1) {
      return mylist(Mycons{a0, std::make_shared<mylist>(std::move(a1))});
    }

    static mylist mynil() { return mylist(Mynil{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, mylist &, T1 &>
  static T1 mylist_rect(F0 &&f, T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f(a0, *a1, mylist_rect<T1>(f, f0, *a1));
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, mylist &, T1 &>
  static T1 mylist_rec(F0 &&f, T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f(a0, *a1, mylist_rec<T1>(f, f0, *a1));
    } else {
      return f0;
    }
  }

  static uint64_t length(const mylist &l);
  /// BUG: The reuse optimization fires and sets d_a1 = l, where l
  /// is the scrutinee (the very node being mutated).
  /// This creates a CYCLE: the node's tail points to itself.
  ///
  /// In Rocq, mycons x l creates a FRESH cons cell whose tail is l.
  /// With reuse, the SAME cell is mutated: d_a1 <- l makes the cell
  /// point to itself.
  ///
  /// Calling length on the result causes infinite recursion -> stack overflow.
  ///
  /// Reuse fires because:
  /// 1. l escapes in else l -> owned
  /// 2. mycons branch tail is mycons with arity 2 = 2
  /// 3. mycons is index 0 -> List.hd picks it
  /// 4. use_count() == 1 for fresh values
  static mylist prepend_self(mylist l, bool b);
  /// test1: prepend_self(1, 2, true) should produce 1, 1, 2.
  /// In Rocq: mycons 1 (mycons 1 (mycons 2 mynil)), length = 3.
  /// With reuse bug: mycons 1 -> itself (cycle), length = infinite loop.
  static inline const uint64_t test1 = length(prepend_self(
      mylist::mycons(UINT64_C(1), mylist::mycons(UINT64_C(2), mylist::mynil())),
      true));
  /// test2: Even simpler - single element list.
  /// prepend_self(42, true) should produce 42, 42, length = 2.
  /// With bug: 42 -> itself, length = infinite.
  static inline const uint64_t test2 =
      length(prepend_self(mylist::mycons(UINT64_C(42), mylist::mynil()), true));
};

#endif // INCLUDED_REUSE_SELF_CYCLE
