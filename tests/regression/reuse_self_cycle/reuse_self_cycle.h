#ifndef INCLUDED_REUSE_SELF_CYCLE
#define INCLUDED_REUSE_SELF_CYCLE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ReuseSelfCycle {
  /// mycons at index 0 so reuse fires on the mycons branch.
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
  static mylist prepend_self(mylist l, const bool &b);
  /// test1: prepend_self(1, 2, true) should produce 1, 1, 2.
  /// In Rocq: mycons 1 (mycons 1 (mycons 2 mynil)), length = 3.
  /// With reuse bug: mycons 1 -> itself (cycle), length = infinite loop.
  static inline const unsigned int test1 = length(prepend_self(
      mylist::mycons(1u, mylist::mycons(2u, mylist::mynil())), true));
  /// test2: Even simpler - single element list.
  /// prepend_self(42, true) should produce 42, 42, length = 2.
  /// With bug: 42 -> itself, length = infinite.
  static inline const unsigned int test2 =
      length(prepend_self(mylist::mycons(42u, mylist::mynil()), true));
};

#endif // INCLUDED_REUSE_SELF_CYCLE
