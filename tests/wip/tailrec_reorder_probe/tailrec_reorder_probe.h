#ifndef INCLUDED_TAILREC_REORDER_PROBE
#define INCLUDED_TAILREC_REORDER_PROBE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct TailrecReorderProbe {
  /// Custom list to control exact code generation.
  template <typename t_A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      t_A d_a0;
      std::shared_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mylist<t_A>> mynil() {
      return std::make_shared<mylist<t_A>>(Mynil{});
    }

    static std::shared_ptr<mylist<t_A>>
    mycons(t_A a0, const std::shared_ptr<mylist<t_A>> &a1) {
      return std::make_shared<mylist<t_A>>(Mycons{std::move(a0), a1});
    }

    static std::shared_ptr<mylist<t_A>>
    mycons(t_A a0, std::shared_ptr<mylist<t_A>> &&a1) {
      return std::make_shared<mylist<t_A>>(
          Mycons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<mylist<T1>>, T2> F1>
  static T2 mylist_rect(const T2 f, F1 &&f0,
                        const std::shared_ptr<mylist<T1>> &m) {
    struct _Enter {
      const std::shared_ptr<mylist<T1>> m;
    };

    struct _Call1 {
      std::shared_ptr<mylist<T1>> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<mylist<T1>> m = _f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m->v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(m->v());
          _stack.emplace_back(_Call1{d_a1, d_a0});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<mylist<T1>>, T2> F1>
  static T2 mylist_rec(const T2 f, F1 &&f0,
                       const std::shared_ptr<mylist<T1>> &m) {
    struct _Enter {
      const std::shared_ptr<mylist<T1>> m;
    };

    struct _Call1 {
      std::shared_ptr<mylist<T1>> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<mylist<T1>> m = _f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m->v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(m->v());
          _stack.emplace_back(_Call1{d_a1, d_a0});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  /// Tail-recursive reverse via accumulator.
  ///
  /// BUG HYPOTHESIS: When loopified, the assignments to loop variables
  /// l := t and acc := mycons h acc must happen in the right order.
  /// If l := t fires first, the old list node may be freed (when
  /// use_count drops to 0), making h a dangling reference in the
  /// subsequent mycons h acc construction.
  ///
  /// This is a potential evaluation-order / use-after-free bug in the
  /// loopify pass.
  template <typename T1>
  static std::shared_ptr<mylist<T1>>
  my_rev_append(const std::shared_ptr<mylist<T1>> &l,
                std::shared_ptr<mylist<T1>> acc) {
    std::shared_ptr<mylist<T1>> _result;
    std::shared_ptr<mylist<T1>> _loop_acc = std::move(acc);
    std::shared_ptr<mylist<T1>> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename mylist<T1>::Mynil>(_loop_l->v())) {
        _result = std::move(_loop_acc);
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<T1>::Mycons>(_loop_l->v());
        std::shared_ptr<mylist<T1>> _next_acc =
            mylist<T1>::mycons(d_a0, _loop_acc);
        std::shared_ptr<mylist<T1>> _next_l = d_a1;
        _loop_acc = std::move(_next_acc);
        _loop_l = std::move(_next_l);
      }
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<mylist<T1>>
  my_reverse(const std::shared_ptr<mylist<T1>> &l) {
    return my_rev_append<T1>(l, mylist<T1>::mynil());
  }

  /// Variant: TWO arguments depend on pattern-matched fields.
  /// l := t, acc1 := mycons h acc1, acc2 := mycons (h+1) acc2
  /// Both acc1 and acc2 need h from the OLD l.
  __attribute__((pure)) static std::pair<std::shared_ptr<mylist<unsigned int>>,
                                         std::shared_ptr<mylist<unsigned int>>>
  dual_accum(const std::shared_ptr<mylist<unsigned int>> &l,
             std::shared_ptr<mylist<unsigned int>> acc1,
             std::shared_ptr<mylist<unsigned int>> acc2);

  template <typename T1, MapsTo<unsigned int, T1> F0>
  __attribute__((pure)) static unsigned int
  mylist_sum(F0 &&f, const std::shared_ptr<mylist<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<mylist<T1>> l;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<mylist<T1>> l = _f.l;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(l->v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(l->v());
          _stack.emplace_back(_Call1{f(d_a0)});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = (_f._s0 + _result);
      }
    }
    return _result;
  }

  static inline const unsigned int test_rev = mylist_sum<unsigned int>(
      [](const unsigned int x) { return x; },
      my_reverse<unsigned int>(mylist<unsigned int>::mycons(
          1u, mylist<unsigned int>::mycons(
                  2u, mylist<unsigned int>::mycons(
                          3u, mylist<unsigned int>::mynil())))));
  static inline const unsigned int test_dual = []() -> unsigned int {
    auto _cs = dual_accum(
        mylist<unsigned int>::mycons(
            10u, mylist<unsigned int>::mycons(
                     20u, mylist<unsigned int>::mycons(
                              30u, mylist<unsigned int>::mynil()))),
        mylist<unsigned int>::mynil(), mylist<unsigned int>::mynil());
    const std::shared_ptr<mylist<unsigned int>> &a = _cs.first;
    const std::shared_ptr<mylist<unsigned int>> &b = _cs.second;
    return (
        mylist_sum<unsigned int>([](const unsigned int x) { return x; }, a) +
        mylist_sum<unsigned int>([](const unsigned int x) { return x; }, b));
  }();
  /// Tail-recursive function where the recursive argument is a COMPLEX
  /// expression involving multiple pattern variables.
  static std::shared_ptr<mylist<unsigned int>>
  weave(const std::shared_ptr<mylist<unsigned int>> &l1,
        const std::shared_ptr<mylist<unsigned int>> &l2,
        std::shared_ptr<mylist<unsigned int>> acc);
  static inline const unsigned int test_weave = mylist_sum<unsigned int>(
      [](const unsigned int x) { return x; },
      weave(mylist<unsigned int>::mycons(
                1u, mylist<unsigned int>::mycons(
                        3u, mylist<unsigned int>::mynil())),
            mylist<unsigned int>::mycons(
                2u, mylist<unsigned int>::mycons(
                        4u, mylist<unsigned int>::mynil())),
            mylist<unsigned int>::mynil()));
};

#endif // INCLUDED_TAILREC_REORDER_PROBE
