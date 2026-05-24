#ifndef INCLUDED_REUSE_FN_IN_BODY
#define INCLUDED_REUSE_FN_IN_BODY

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct ReuseFnInBody {
  /// mycons first so reuse picks it (variant index 0).
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
  static uint64_t sum(const mylist &l);
  /// BUG: reuse fires on the mycons branch. The body constructs
  /// mycons (sum l + h) t where l is the scrutinee.
  ///
  /// The reuse path does:
  /// auto h  = std::move(_rf.d_a0);
  /// auto xs = std::move(_rf.d_a1);   // _rf.d_a1 = nullptr
  /// _rf.d_a0 = sum(l) + h;           // sum(l) accesses l.d_a1 = nullptr!
  /// _rf.d_a1 = xs;
  /// return l;
  ///
  /// sum(l) traverses l, hitting the null d_a1 field.
  /// Dereferencing null shared_ptr → CRASH.
  ///
  /// This is similar to reuse_use_after_move but the scrutinee
  /// is used through a DIFFERENT function (sum instead of length)
  /// AND combined with a pattern variable in an arithmetic expression.
  static mylist prefix_sum(mylist l, bool b);
  static inline const uint64_t test1 = sum(prefix_sum(
      mylist::mycons(
          UINT64_C(1),
          mylist::mycons(UINT64_C(2),
                         mylist::mycons(UINT64_C(3), mylist::mynil()))),
      true));
  /// Original list: 1, 2, 3. sum = 6.
  /// prefix_sum: head becomes sum(1,2,3) + 1 = 6 + 1 = 7, tail = 2, 3.
  /// Result: 7, 2, 3. sum = 12.
  /// BUG: sum(l) crashes because l's fields are moved.
  static inline const uint64_t test2 =
      sum(prefix_sum(mylist::mycons(UINT64_C(10), mylist::mynil()), true));
};

#endif // INCLUDED_REUSE_FN_IN_BODY
