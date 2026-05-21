#ifndef INCLUDED_REUSE_SELF_CYCLE
#define INCLUDED_REUSE_SELF_CYCLE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

    mylist(const mylist &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist &&_other) noexcept : v_(std::move(_other.v_)) {}

    mylist &operator=(const mylist &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist &operator=(mylist &&_other) noexcept {
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
              Mycons{_alt.a0, _alt.a1 ? std::make_shared<mylist>() : nullptr};
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
    static mylist mycons(uint64_t a0, mylist a1) {
      return mylist(Mycons{a0, std::make_shared<mylist>(std::move(a1))});
    }

    static mylist mynil() { return mylist(Mynil{}); }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::shared_ptr<mylist>> _stack{};
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
