#ifndef INCLUDED_FIX_MOVE_CAPTURE
#define INCLUDED_FIX_MOVE_CAPTURE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
      unsigned int d_a0;
      std::unique_ptr<mylist> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    mylist(const mylist &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist &&_other) : d_v_(std::move(_other.d_v_)) {}

    mylist &operator=(const mylist &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    mylist &operator=(mylist &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    mylist clone() const {
      mylist _out{};

      struct _CloneFrame {
        const mylist *_src;
        mylist *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist *_src = _frame._src;
        mylist *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          _dst->d_v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->d_v_ = Mycons{_alt.d_a0,
                              _alt.d_a1 ? std::make_unique<mylist>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static mylist mynil() { return mylist(Mynil{}); }

    static mylist mycons(unsigned int a0, mylist a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist>> _stack{};
      auto _drain = [&](mylist &_node) {
        if (std::holds_alternative<Mycons>(_node.d_v_)) {
          auto &_alt = std::get<Mycons>(_node.d_v_);
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F1>
  static T1 mylist_rect(const T1 f0, F1 &&f1, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mynil>(m.v())) {
      return f0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(m.v());
      return f1(d_a0, *(d_a1), mylist_rect<T1>(f0, f1, *(d_a1)));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F1>
  static T1 mylist_rec(const T1 f0, F1 &&f1, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mynil>(m.v())) {
      return f0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(m.v());
      return f1(d_a0, *(d_a1), mylist_rec<T1>(f0, f1, *(d_a1)));
    }
  }

  static unsigned int length(const mylist &l);
  static unsigned int sum(const mylist &l);
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
  static unsigned int f(mylist l);
  static inline const unsigned int test1 = f(mylist::mycons(
      10u, mylist::mycons(20u, mylist::mycons(30u, mylist::mynil()))));
  /// Even simpler: use the fixpoint, then pass l to a consuming
  /// function. The addition's evaluation order is unspecified in C++,
  /// so we use a let-binding to force the order.
  static unsigned int f2(mylist l);
  static inline const unsigned int test2 =
      f2(mylist::mycons(5u, mylist::mycons(15u, mylist::mynil())));
};

#endif // INCLUDED_FIX_MOVE_CAPTURE
