#ifndef INCLUDED_REUSE_FN_IN_BODY
#define INCLUDED_REUSE_FN_IN_BODY

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ReuseFnInBody {
  /// mycons first so reuse picks it (variant index 0).
  struct mylist {
    // TYPES
    struct Mycons {
      unsigned int d_a0;
      std::unique_ptr<mylist> d_a1;
    };

    struct Mynil {};

    using variant_t = std::variant<Mycons, Mynil>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

    mylist(const mylist &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) mylist &operator=(const mylist &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) mylist &operator=(mylist &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) mylist clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Mycons>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<Mycons>(_sv.v());
        return mylist(Mycons{
            d_a0, d_a1 ? std::make_unique<ReuseFnInBody::mylist>(d_a1->clone())
                       : nullptr});
      } else {
        return mylist(Mynil{});
      }
    }

    // CREATORS
    __attribute__((pure)) static mylist mycons(unsigned int a0,
                                               const mylist &a1) {
      return mylist(Mycons{std::move(a0), std::make_unique<mylist>(a1)});
    }

    __attribute__((pure)) static mylist mynil() { return mylist(Mynil{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) mylist *operator->() { return this; }

    __attribute__((pure)) const mylist *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = mylist(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F0>
  static T1 mylist_rect(F0 &&f, const T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(m.v());
      return f(d_a0, *(d_a1), mylist_rect<T1>(f, f0, *(d_a1)));
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F0>
  static T1 mylist_rec(F0 &&f, const T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(m.v());
      return f(d_a0, *(d_a1), mylist_rec<T1>(f, f0, *(d_a1)));
    } else {
      return f0;
    }
  }

  __attribute__((pure)) static unsigned int length(const mylist &l);
  __attribute__((pure)) static unsigned int sum(const mylist &l);
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
  __attribute__((pure)) static mylist prefix_sum(mylist l, const bool &b);
  static inline const unsigned int test1 = sum(prefix_sum(
      mylist::mycons(1u,
                     mylist::mycons(2u, mylist::mycons(3u, mylist::mynil()))),
      true));
  /// Original list: 1, 2, 3. sum = 6.
  /// prefix_sum: head becomes sum(1,2,3) + 1 = 6 + 1 = 7, tail = 2, 3.
  /// Result: 7, 2, 3. sum = 12.
  /// BUG: sum(l) crashes because l's fields are moved.
  static inline const unsigned int test2 =
      sum(prefix_sum(mylist::mycons(10u, mylist::mynil()), true));
};

#endif // INCLUDED_REUSE_FN_IN_BODY
