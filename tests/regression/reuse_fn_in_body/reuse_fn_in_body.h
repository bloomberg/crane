#ifndef INCLUDED_REUSE_FN_IN_BODY
#define INCLUDED_REUSE_FN_IN_BODY

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct ReuseFnInBody {
  /// mycons first so reuse picks it (variant index 0).
  struct mylist {
    // TYPES
    struct Mycons {
      unsigned int a0;
      std::unique_ptr<mylist> a1;
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

    mylist(const mylist &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist &&_other) : v_(std::move(_other.v_)) {}

    mylist &operator=(const mylist &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist &operator=(mylist &&_other) {
      v_ = std::move(_other.v_);
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
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist *_src = _frame._src;
        mylist *_dst = _frame._dst;
        if (std::holds_alternative<Mycons>(_src->v())) {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->v_ =
              Mycons{_alt.a0, _alt.a1 ? std::make_unique<mylist>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          _dst->v_ = Mynil{};
        }
      }
      return _out;
    }

    // CREATORS
    static mylist mycons(unsigned int a0, mylist a1) {
      return mylist(Mycons{a0, std::make_unique<mylist>(std::move(a1))});
    }

    static mylist mynil() { return mylist(Mynil{}); }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist &_node) {
        if (std::holds_alternative<Mycons>(_node.v_)) {
          auto &_alt = std::get<Mycons>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
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

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, mylist &, T1 &>
  static T1 mylist_rect(F0 &&f, T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f(a0, *a1, mylist_rect<T1>(f, f0, *a1));
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, mylist &, T1 &>
  static T1 mylist_rec(F0 &&f, T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f(a0, *a1, mylist_rec<T1>(f, f0, *a1));
    } else {
      return f0;
    }
  }

  static unsigned int length(const mylist &l);
  static unsigned int sum(const mylist &l);
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
