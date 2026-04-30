#ifndef INCLUDED_REUSE_FN_IN_BODY
#define INCLUDED_REUSE_FN_IN_BODY

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
        if (std::holds_alternative<Mycons>(_src->v())) {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->d_v_ = Mycons{_alt.d_a0,
                              _alt.d_a1 ? std::make_unique<mylist>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else {
          _dst->d_v_ = Mynil{};
        }
      }
      return _out;
    }

    // CREATORS
    static mylist mycons(unsigned int a0, mylist a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist>(std::move(a1))});
    }

    static mylist mynil() { return mylist(Mynil{}); }

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
  static mylist prefix_sum(mylist l, const bool &b);
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
