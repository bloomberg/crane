#ifndef INCLUDED_LET_PAIR_SHADOW
#define INCLUDED_LET_PAIR_SHADOW

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct LetPairShadow {
  /// BUG: Two sequential let '(a, b) := f x destructurings of COMPUTED
  /// pair results in the same scope both generate the C++ temporary name
  /// _cs. The second declaration shadows the first, producing invalid
  /// C++ (redefinition error).
  ///
  /// Root cause: the pair-destructuring temporary _cs is not uniquified
  /// per destructuring site. Each let '(x, y) := expr where expr is
  /// a function call emits:
  /// auto _cs = expr;
  /// const T& x = _cs.first;
  /// const T& y = _cs.second;
  /// When two such destructurings appear in sequence, the second
  /// auto _cs = ... collides with the first.
  ///
  /// Note: simple variable RHS (let '(x,y) := p) does NOT create a
  /// temporary — it accesses p.first/p.second directly. The bug
  /// only fires when the RHS is a computed expression (function call,
  /// constructor application, etc.).
  ///
  /// This is a codegen/compilation-failure bug.
  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::shared_ptr<mylist<A>> a1;
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

    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ = Mycons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::shared_ptr<mylist<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
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

  static uint64_t mylist_sum(const mylist<uint64_t> &l);

  /// Pattern 1: map_accum — two sequential pair destructurings of
  /// function-call results in the same match branch.
  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::pair<T3, T2>, F0 &, T3 &, T1 &>
  static std::pair<mylist<T2>, T3> map_accum(F0 &&f, T3 acc,
                                             const mylist<T1> &l) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
      return std::make_pair(mylist<T2>::mynil(), acc);
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l.v());
      auto _cs = f(acc, a0);
      T3 new_acc = std::move(_cs.first);
      T2 y = std::move(_cs.second);
      auto _cs1 = map_accum<T1, T2, T3>(f, new_acc, *a1);
      mylist<T2> rest = std::move(_cs1.first);
      T3 final_acc = std::move(_cs1.second);
      return std::make_pair(mylist<T2>::mycons(y, std::move(rest)), final_acc);
    }
  }

  /// test1: map_accum with running sum.
  /// f(acc, x) = (acc+x, acc).
  /// map_accum f 0 10,20,30 = (0,10,30, 60)
  /// sum(list) + acc = 40 + 60 = 100
  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = map_accum<uint64_t, uint64_t, uint64_t>(
        [](uint64_t s, uint64_t x) { return std::make_pair((s + x), s); },
        UINT64_C(0),
        mylist<uint64_t>::mycons(
            UINT64_C(10),
            mylist<uint64_t>::mycons(
                UINT64_C(20), mylist<uint64_t>::mycons(
                                  UINT64_C(30), mylist<uint64_t>::mynil()))));
    mylist<uint64_t> l = std::move(_cs.first);
    uint64_t acc = std::move(_cs.second);
    return (mylist_sum(std::move(l)) + acc);
  }();
  /// Helper functions that return pairs (force temporary allocation).
  static std::pair<uint64_t, uint64_t> add_pair(uint64_t a, uint64_t b);
  static std::pair<uint64_t, uint64_t> sub_pair(uint64_t a, uint64_t b);
  /// Pattern 2: Two destructs of function-call results in top-level body.
  static uint64_t double_call_destruct(uint64_t a, uint64_t b, uint64_t c,
                                       uint64_t d);
  /// test2: add_pair 3 4 = (7, 12), sub_pair 10 3 = (7, 13)
  /// 7 + 12 + 7 + 13 = 39
  static inline const uint64_t test2 =
      double_call_destruct(UINT64_C(3), UINT64_C(4), UINT64_C(10), UINT64_C(3));
  /// Pattern 3: Three destructs of function-call results.
  static uint64_t triple_call_destruct(uint64_t a, uint64_t b, uint64_t c,
                                       uint64_t d, uint64_t e, uint64_t f);
  /// test3: add_pair 1 2 = (3,2), add_pair 3 4 = (7,12),
  /// add_pair 5 6 = (11,30).  3+2+7+12+11+30 = 65
  static inline const uint64_t test3 =
      triple_call_destruct(UINT64_C(1), UINT64_C(2), UINT64_C(3), UINT64_C(4),
                           UINT64_C(5), UINT64_C(6));
};

#endif // INCLUDED_LET_PAIR_SHADOW
