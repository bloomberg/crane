#ifndef INCLUDED_TAILREC_REORDER_PROBE
#define INCLUDED_TAILREC_REORDER_PROBE

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct TailrecReorderProbe {
  /// Custom list to control exact code generation.
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

    template <typename CraneU>
    mylist(const mylist<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename mylist<CraneU>::Mynil>(
                    _other.v())) {
              return Mynil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename mylist<CraneU>::Mycons>(_other.v());
              return Mycons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<mylist<A>>(
                            crane_convert<mylist<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist<A>(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<mylist<A>> {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<mylist<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    mylist(const mylist &) = default;
    mylist &operator=(const mylist &) = default;
    mylist(mylist &&) = default;
    mylist &operator=(mylist &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, mylist<T1> &, T2 &>
  static T2
  mylist_rect(T2 f, F1 &&f0,
              const mylist<T1> &m) { /// CraneEnter: captures varying parameters
                                     /// for each recursive call.

    struct CraneEnter {
      const mylist<T1> *m;
    };

    /// CraneCont_Mycons: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Mycons {
      T1 a0;
      std::shared_ptr<mylist<T1>> a1;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
    T2 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&m});
    /// Loopified mylist_rect: CraneEnter -> CraneCont_Mycons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const mylist<T1> &m = *_f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
          _stack.emplace_back(CraneCont_Mycons{a0, a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
        auto a0 = std::move(_f.a0);
        std::shared_ptr<mylist<T1>> a1 = std::move(_f.a1);
        _result = f0(a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, mylist<T1> &, T2 &>
  static T2
  mylist_rec(T2 f, F1 &&f0,
             const mylist<T1> &m) { /// CraneEnter: captures varying parameters
                                    /// for each recursive call.

    struct CraneEnter {
      const mylist<T1> *m;
    };

    /// CraneCont_Mycons: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Mycons {
      T1 a0;
      std::shared_ptr<mylist<T1>> a1;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
    T2 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&m});
    /// Loopified mylist_rec: CraneEnter -> CraneCont_Mycons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const mylist<T1> &m = *_f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
          _stack.emplace_back(CraneCont_Mycons{a0, a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
        auto a0 = std::move(_f.a0);
        std::shared_ptr<mylist<T1>> a1 = std::move(_f.a1);
        _result = f0(a0, *a1, std::move(_result));
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
  static mylist<T1> my_rev_append(const mylist<T1> &l, mylist<T1> acc) {
    mylist<T1> _loop_acc = std::move(acc);
    const mylist<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename mylist<T1>::Mynil>(_loop_l->v())) {
        return _loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<T1>::Mycons>(_loop_l->v());
        _loop_acc = mylist<T1>::mycons(a0, std::move(_loop_acc));
        _loop_l = crane_raw(a1);
      }
    }
  }

  template <typename T1> static mylist<T1> my_reverse(const mylist<T1> &l) {
    return my_rev_append<T1>(l, mylist<T1>::mynil());
  }

  /// Variant: TWO arguments depend on pattern-matched fields.
  /// l := t, acc1 := mycons h acc1, acc2 := mycons (h+1) acc2
  /// Both acc1 and acc2 need h from the OLD l.
  static std::pair<mylist<uint64_t>, mylist<uint64_t>>
  dual_accum(const mylist<uint64_t> &l, const mylist<uint64_t> &acc1,
             const mylist<uint64_t> &acc2);

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, T1 &>
  static uint64_t
  mylist_sum(F0 &&f,
             const mylist<T1> &l) { /// CraneEnter: captures varying parameters
                                    /// for each recursive call.

    struct CraneEnter {
      const mylist<T1> *l;
    };

    /// CraneCont_Mycons: saves [a0], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Mycons {
      T1 a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified mylist_sum: CraneEnter -> CraneCont_Mycons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const mylist<T1> &l = *_f.l;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l.v());
          _stack.emplace_back(CraneCont_Mycons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
        auto a0 = std::move(_f.a0);
        _result = (f(a0) + std::move(_result));
      }
    }
    return _result;
  }

  static inline const uint64_t test_rev = mylist_sum<uint64_t>(
      [](uint64_t x) { return x; },
      my_reverse<uint64_t>(mylist<uint64_t>::mycons(
          UINT64_C(1),
          mylist<uint64_t>::mycons(
              UINT64_C(2), mylist<uint64_t>::mycons(
                               UINT64_C(3), mylist<uint64_t>::mynil())))));
  static inline const uint64_t test_dual = []() -> uint64_t {
    auto [a, b] = dual_accum(
        mylist<uint64_t>::mycons(
            UINT64_C(10),
            mylist<uint64_t>::mycons(
                UINT64_C(20), mylist<uint64_t>::mycons(
                                  UINT64_C(30), mylist<uint64_t>::mynil()))),
        mylist<uint64_t>::mynil(), mylist<uint64_t>::mynil());
    return (mylist_sum<uint64_t>([](uint64_t x) { return x; }, std::move(a)) +
            mylist_sum<uint64_t>([](uint64_t x) { return x; }, std::move(b)));
  }();
  /// Tail-recursive function where the recursive argument is a COMPLEX
  /// expression involving multiple pattern variables.
  static mylist<uint64_t> weave(const mylist<uint64_t> &l1,
                                const mylist<uint64_t> &l2,
                                const mylist<uint64_t> &acc);

  static inline const uint64_t test_weave = mylist_sum<uint64_t>(
      [](uint64_t x) { return x; },
      weave(mylist<uint64_t>::mycons(
                UINT64_C(1), mylist<uint64_t>::mycons(
                                 UINT64_C(3), mylist<uint64_t>::mynil())),
            mylist<uint64_t>::mycons(
                UINT64_C(2), mylist<uint64_t>::mycons(
                                 UINT64_C(4), mylist<uint64_t>::mynil())),
            mylist<uint64_t>::mynil()));
};

#endif // INCLUDED_TAILREC_REORDER_PROBE
