#ifndef INCLUDED_CLOSURE_MAP_ESCAPE
#define INCLUDED_CLOSURE_MAP_ESCAPE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct ClosureMapEscape {
  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::unique_ptr<mylist<A>> a1;
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

    mylist(const mylist<A> &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    mylist<A> &operator=(const mylist<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist<A> &operator=(mylist<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    mylist<A> clone() const {
      mylist<A> _out{};

      struct _CloneFrame {
        const mylist<A> *_src;
        mylist<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist<A> *_src = _frame._src;
        mylist<A> *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          _dst->v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->v_ = Mycons{_alt.a0,
                            _alt.a1 ? std::make_unique<mylist<A>>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ =
            Mycons{A(a0), a1 ? std::make_unique<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist<A> &_node) {
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

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, mylist<T1> &, T2 &>
  static T2 mylist_rect(T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(a0, *a1, mylist_rect<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, mylist<T1> &, T2 &>
  static T2 mylist_rec(T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(a0, *a1, mylist_rec<T1, T2>(f, f0, *a1));
    }
  }

  /// Build a list of closures from a list of nats using LOCAL FIXPOINTS.
  /// Each recursive call creates a fixpoint add that captures the
  /// pattern variable h from the match.
  ///
  /// BUG: Each local fixpoint uses & capture. The pattern variable h
  /// is a local binding within the match IIFE. The fixpoint is stored in
  /// mycons (a constructor), so return_captures_by_value does NOT
  /// apply. After the match, h goes out of scope, and the closure
  /// references dangling memory.
  ///
  /// Difference from fix_escape_match: uses a USER-DEFINED list type
  /// (not stdlib option), and the fixpoints are built RECURSIVELY
  /// from list elements (not a single fixpoint).
  static mylist<std::function<unsigned int(unsigned int)>>
  map_to_adders(const mylist<unsigned int> &l);
  static unsigned int
  apply_first(const mylist<std::function<unsigned int(unsigned int)>> &fns,
              unsigned int arg);
  static unsigned int sum_apply(
      const mylist<std::function<unsigned int(unsigned int)>> &fns,
      unsigned int arg); /// test1: map_to_adders 10, 20, 30, apply first to 5.
  /// add(5) where add(x) = x + 10. So 10 + 5 = 15.
  /// Bug: h=10 captured by &, dangling after match.
  static inline const unsigned int test1 =
      apply_first(map_to_adders(mylist<unsigned int>::mycons(
                      10u, mylist<unsigned int>::mycons(
                               20u, mylist<unsigned int>::mycons(
                                        30u, mylist<unsigned int>::mynil())))),
                  5u);
  /// test2: Sum of applying all adders to 0.
  /// (0+10) + (0+20) + (0+30) = 60.
  static inline const unsigned int test2 =
      sum_apply(map_to_adders(mylist<unsigned int>::mycons(
                    10u, mylist<unsigned int>::mycons(
                             20u, mylist<unsigned int>::mycons(
                                      30u, mylist<unsigned int>::mynil())))),
                0u);
  /// test3: Build adders, noise, then apply.
  /// (1+100) + (1+200) = 302.
  static inline const unsigned int test3 = []() {
    mylist<std::function<unsigned int(unsigned int)>> fns =
        map_to_adders(mylist<unsigned int>::mycons(
            100u,
            mylist<unsigned int>::mycons(200u, mylist<unsigned int>::mynil())));
    return sum_apply(std::move(fns), 1u);
  }();
};

#endif // INCLUDED_CLOSURE_MAP_ESCAPE
