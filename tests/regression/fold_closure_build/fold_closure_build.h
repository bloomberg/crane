#ifndef INCLUDED_FOLD_CLOSURE_BUILD
#define INCLUDED_FOLD_CLOSURE_BUILD

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

    mylist(mylist<A> &&_other) : v_(std::move(_other.v_)) {}

    mylist<A> &operator=(const mylist<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist<A> &operator=(mylist<A> &&_other) {
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
  static unsigned int compose_adders(const mylist<unsigned int> &l,
                                     unsigned int _x0);
  /// test1: compose_adders 10,20,30 7 = 67
  static inline const unsigned int test1 = compose_adders(
      mylist<unsigned int>::mycons(
          10u, mylist<unsigned int>::mycons(
                   20u, mylist<unsigned int>::mycons(
                            30u, mylist<unsigned int>::mynil()))),
      7u);
  /// Pattern 2: Store the composed function and call it TWICE.
  /// If the closure chain has dangling references, the second call
  /// might read clobbered stack memory.
  static inline const unsigned int test2 = []() {
    std::function<unsigned int(unsigned int)> f =
        [](unsigned int _x0) -> unsigned int {
      return compose_adders(mylist<unsigned int>::mycons(
                                5u, mylist<unsigned int>::mycons(
                                        10u, mylist<unsigned int>::mynil())),
                            _x0);
    };
    return (f(0u) + f(100u));
  }();
  /// Pattern 3: Fold producing a list of closures (not composing them).
  /// Each closure captures the list element from the fold iteration.
  static mylist<std::function<unsigned int(unsigned int)>>
  collect_adders(const mylist<unsigned int> &l);
  static unsigned int
  apply_all(const mylist<std::function<unsigned int(unsigned int)>> &fns,
            unsigned int x); /// test3: collect_adders 10,20,30
  /// = (30+_), (20+_), (10+_)  (reversed by fold_left)
  /// apply_all with x=5: (30+5) + (20+5) + (10+5) = 75
  static inline const unsigned int test3 =
      apply_all(collect_adders(mylist<unsigned int>::mycons(
                    10u, mylist<unsigned int>::mycons(
                             20u, mylist<unsigned int>::mycons(
                                      30u, mylist<unsigned int>::mynil())))),
                5u);
  /// Pattern 4: Fold with a FIXPOINT as accumulator.
  /// The fixpoint captures both acc and h from the fold callback.
  ///
  /// BUG HYPOTHESIS: The fixpoint go uses & to capture acc and h.
  /// acc is the std::function accumulator from fold_left.
  /// h is the current list element.
  /// Both are locals in the fold callback's scope.
  /// When fold returns, these scopes are destroyed, but the
  /// final fixpoint (stored in the accumulator) still references them.
  static unsigned int compose_with_fix(const mylist<unsigned int> &l,
                                       unsigned int _x0);
  /// test4: compose_with_fix 10
  /// first iteration: acc=id, h=10
  /// go(x) = x + acc(h) = x + id(10) = x + 10
  /// test4 = go(5) = 5 + 10 = 15
  static inline const unsigned int test4 = compose_with_fix(
      mylist<unsigned int>::mycons(10u, mylist<unsigned int>::mynil()), 5u);
  /// test5: compose_with_fix 10, 20
  /// first: acc=id, h=10, go1(x) = x + id(10) = x + 10
  /// second: acc=go1, h=20, go2(x) = x + go1(20) = x + 30
  /// test5 = go2(7) = 7 + 30 = 37
  static inline const unsigned int test5 = compose_with_fix(
      mylist<unsigned int>::mycons(
          10u,
          mylist<unsigned int>::mycons(20u, mylist<unsigned int>::mynil())),
      7u);
};

#endif // INCLUDED_FOLD_CLOSURE_BUILD
