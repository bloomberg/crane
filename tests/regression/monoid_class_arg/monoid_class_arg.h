#ifndef INCLUDED_MONOID_CLASS_ARG
#define INCLUDED_MONOID_CLASS_ARG

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &&>
  T1 fold_right(F0 &&f, T1 a0) const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: saves [a1], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      A a1;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified fold_right: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = a0;
        } else {
          const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a1 = std::move(_f.a1);
        _result = f(a1, std::move(_result));
      }
    }
    return _result;
  }

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};

template <typename I, typename A>
concept Monoid = requires {
  { I::unit_() } -> std::convertible_to<A>;
  { I::op(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<A>;
};

struct MonoidClassArg {
  struct MNat {
    static uint64_t unit_() { return UINT64_C(0); }

    static uint64_t op(uint64_t a0, uint64_t a1) { return (a0 + a1); }
  };

  static_assert(Monoid<MNat, uint64_t>);

  template <typename T1> struct MList {
    static List<T1> unit_() { return List<T1>::nil(); }

    static List<T1> op(List<T1> a0, List<T1> a1) {
      return a0.app(std::move(a1));
    }
  };

  template <typename _tcI0, typename _tcI1, typename T1, typename T2>
    requires Monoid<_tcI0, T1> && Monoid<_tcI1, T2>
  struct MPair {
    static std::pair<T1, T2> unit_() {
      return std::make_pair(_tcI0::unit_(), _tcI1::unit_());
    }

    static std::pair<T1, T2> op(std::pair<T1, T2> p, std::pair<T1, T2> q) {
      return std::make_pair(
          _tcI0::op(std::move(p).first, std::move(q).first),
          _tcI1::op(std::move(p).second, std::move(q).second));
    }
  };

  template <typename _tcI0, typename T1>
    requires Monoid<_tcI0, T1>
  static T1 mconcat(const List<T1> &l) {
    return l.template fold_right<T1>(_tcI0::op, _tcI0::unit_());
  }

  static inline const uint64_t run =
      ((mconcat<MNat, uint64_t>(List<uint64_t>::cons(
            UINT64_C(1),
            List<uint64_t>::cons(
                UINT64_C(2),
                List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())))) +
        mconcat<MList<uint64_t>, List<uint64_t>>(
            List<List<uint64_t>>::cons(
                List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()),
                List<List<uint64_t>>::cons(
                    List<uint64_t>::cons(
                        UINT64_C(2), List<uint64_t>::cons(
                                         UINT64_C(3), List<uint64_t>::nil())),
                    List<List<uint64_t>>::nil())))
            .length()) +
       mconcat<MPair<MNat, MList<uint64_t>, uint64_t, List<uint64_t>>,
               std::pair<uint64_t, List<uint64_t>>>(
           List<std::pair<uint64_t, List<uint64_t>>>::cons(
               std::make_pair(
                   UINT64_C(1),
                   List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil())),
               List<std::pair<uint64_t, List<uint64_t>>>::cons(
                   std::make_pair(UINT64_C(2),
                                  List<uint64_t>::cons(UINT64_C(2),
                                                       List<uint64_t>::nil())),
                   List<std::pair<uint64_t, List<uint64_t>>>::nil())))
           .first);
};

#endif // INCLUDED_MONOID_CLASS_ARG
