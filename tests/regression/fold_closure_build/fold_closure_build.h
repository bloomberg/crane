#ifndef INCLUDED_FOLD_CLOSURE_BUILD
#define INCLUDED_FOLD_CLOSURE_BUILD

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct FoldClosureBuild {
  /// FOLD-BASED CLOSURE BUILDING
  ///
  /// BUG HYPOTHESIS: When a fold_left uses its accumulator function
  /// parameter to build closures, the closure for each iteration
  /// captures the fold's function parameter by &. If the fold
  /// function is inlined and the parameter dies after the fold
  /// call returns, the closures hold dangling references.
  ///
  /// This is different from existing wip tests because:
  /// 1. The closures are built INSIDE A FOLD, not in a direct recursive
  /// function
  /// 2. The fold CALLBACK captures pattern variables from the fold's
  /// own match expression, creating a nested scope issue
  /// 3. Multiple closures are chained through the fold, each
  /// depending on the previous one
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
  } /// Simple fold_left.

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T2 &>
  static T1 fold_left(F0 &&f, T1 acc, const mylist<T2> &l) {
    if (std::holds_alternative<typename mylist<T2>::Mynil>(l.v())) {
      return acc;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T2>::Mycons>(l.v());
      return fold_left<T1, T2>(f, f(acc, a0), *a1);
    }
  }

  /// Pattern 1: Build a COMPOSED function via fold.
  /// Each step wraps the accumulator in a new closure.
  ///
  /// Equivalent to:
  /// compose_all 10, 20, 30 id
  /// = fold_left (fun acc h => fun x => acc(h + x)) id 10,20,30
  /// = fun x => id(10 + (20 + (30 + x)))
  /// = fun x => 60 + x
  ///
  /// The inner closure fun x => acc(h+x) captures acc (std::function)
  /// and h (unsigned int). If these are captured by =, safe. By &, dangles.
  static uint64_t compose_adders(const mylist<uint64_t> &l, uint64_t _x0);
  /// test1: compose_adders 10,20,30 7 = 67
  static inline const uint64_t test1 = compose_adders(
      mylist<uint64_t>::mycons(
          UINT64_C(10),
          mylist<uint64_t>::mycons(
              UINT64_C(20), mylist<uint64_t>::mycons(
                                UINT64_C(30), mylist<uint64_t>::mynil()))),
      UINT64_C(7));
  /// Pattern 2: Store the composed function and call it TWICE.
  /// If the closure chain has dangling references, the second call
  /// might read clobbered stack memory.
  static inline const uint64_t test2 = []() {
    std::function<uint64_t(uint64_t)> f = [](uint64_t _x0) -> uint64_t {
      return compose_adders(
          mylist<uint64_t>::mycons(
              UINT64_C(5), mylist<uint64_t>::mycons(UINT64_C(10),
                                                    mylist<uint64_t>::mynil())),
          _x0);
    };
    return (f(UINT64_C(0)) + f(UINT64_C(100)));
  }();
  /// Pattern 3: Fold producing a list of closures (not composing them).
  /// Each closure captures the list element from the fold iteration.
  static mylist<std::function<uint64_t(uint64_t)>>
  collect_adders(const mylist<uint64_t> &l);
  static uint64_t
  apply_all(const mylist<std::function<uint64_t(uint64_t)>> &fns,
            uint64_t x); /// test3: collect_adders 10,20,30
  /// = (30+_), (20+_), (10+_)  (reversed by fold_left)
  /// apply_all with x=5: (30+5) + (20+5) + (10+5) = 75
  static inline const uint64_t test3 = apply_all(
      collect_adders(mylist<uint64_t>::mycons(
          UINT64_C(10),
          mylist<uint64_t>::mycons(
              UINT64_C(20), mylist<uint64_t>::mycons(
                                UINT64_C(30), mylist<uint64_t>::mynil())))),
      UINT64_C(5));
  /// Pattern 4: Fold with a FIXPOINT as accumulator.
  /// The fixpoint captures both acc and h from the fold callback.
  ///
  /// BUG HYPOTHESIS: The fixpoint go uses & to capture acc and h.
  /// acc is the std::function accumulator from fold_left.
  /// h is the current list element.
  /// Both are locals in the fold callback's scope.
  /// When fold returns, these scopes are destroyed, but the
  /// final fixpoint (stored in the accumulator) still references them.
  static uint64_t compose_with_fix(const mylist<uint64_t> &l, uint64_t _x0);
  /// test4: compose_with_fix 10
  /// first iteration: acc=id, h=10
  /// go(x) = x + acc(h) = x + id(10) = x + 10
  /// test4 = go(5) = 5 + 10 = 15
  static inline const uint64_t test4 = compose_with_fix(
      mylist<uint64_t>::mycons(UINT64_C(10), mylist<uint64_t>::mynil()),
      UINT64_C(5));
  /// test5: compose_with_fix 10, 20
  /// first: acc=id, h=10, go1(x) = x + id(10) = x + 10
  /// second: acc=go1, h=20, go2(x) = x + go1(20) = x + 30
  /// test5 = go2(7) = 7 + 30 = 37
  static inline const uint64_t test5 = compose_with_fix(
      mylist<uint64_t>::mycons(
          UINT64_C(10),
          mylist<uint64_t>::mycons(UINT64_C(20), mylist<uint64_t>::mynil())),
      UINT64_C(7));
};

#endif // INCLUDED_FOLD_CLOSURE_BUILD
