#ifndef INCLUDED_LOOPIFY_FRAME_LAMBDA_TYPE
#define INCLUDED_LOOPIFY_FRAME_LAMBDA_TYPE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::template bind<crane::obj, crane::obj>(
        std::declval<typename I::template m<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
};

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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
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
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  uint64_t length() const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
    requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F1 &, T2 &>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
};

/// comb recurses in the first argument of bind, so Set Crane Loopify
/// gives it a frame stack whose resume frame saves the continuation.  The
/// frame declares that field's type as
/// std::decay_t<decltype([](std::pair<...> x0) { ... })> -- the type of a
/// lambda *expression* written inside the struct -- and a lambda expression
/// has a type of its own: the continuation built at the push site is a
/// different closure type, so the push does not compile ("no viable
/// conversion from '(lambda at ...)'").  The body copied into the
/// decltype also stands the captured pattern variables in with
/// std::declval<T1 &>(), which trips libc++'s "std::declval can only be
/// used in an unevaluated context" static assertion, since a lambda body is
/// evaluated.
///
/// Found in Vellvm with the global Set Crane Loopify:
/// Denotation.combine_lists_varargs, 3 of its 59 errors.
struct LoopifyFrameLambdaType {
  template <typename X> struct res {
    // TYPES
    struct Err {};

    struct Ok {
      X x;
    };

    using variant_t = std::variant<Err, Ok>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    res() {}

    explicit res(Err _v) : v_(_v) {}

    explicit res(Ok _v) : v_(std::move(_v)) {}

    template <typename _U>
    res(const res<_U> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename res<_U>::Err>(_other.v())) {
              return Err{};
            } else {
              const auto &[x] = std::get<typename res<_U>::Ok>(_other.v());
              return Ok{[&]() -> X {
                if constexpr (crane_convertible<X, const _U &>) {
                  return crane_convert<X>(x);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            }
          }()) {}

    static res<X> err() { return res<X>(Err{}); }

    static res<X> ok(X x) { return res<X>(Ok{std::move(x)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct Monad_res {
    template <typename _A0> using m = res<_A0>;

    template <typename _A0> static res<_A0> ret(_A0 x) {
      return res<_A0>::ok(std::move(x));
    }

    template <typename _A0, typename _A1>
    static res<_A1> bind(res<_A0> c, crane::fn<res<_A1>(_A0)> k) {
      if (std::holds_alternative<typename res<_A0>::Err>(c.v())) {
        return res<_A1>::err();
      } else {
        const auto &[x0] = std::get<typename res<_A0>::Ok>(c.v());
        return k(x0);
      }
    }
  };

  static_assert(Monad<Monad_res>);

  template <typename T1, typename T2>
  static res<std::pair<List<std::pair<T1, T2>>, List<T2>>>
  comb(const List<T1> &l1,
       const List<T2> &l2) { /// _Enter: captures varying parameters for each
                             /// recursive call.

    struct _Enter {
      const List<T2> *l2;
      const List<T1> *l1;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      crane::fn<res<std::pair<List<std::pair<T1, T2>>, List<T2>>>(
          std::pair<List<std::pair<T1, T2>>, List<T2>>)>
          _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    res<std::pair<List<std::pair<T1, T2>>, List<T2>>> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&l2, &l1});
    /// Loopified comb: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T2> &l2 = *_f.l2;
        const List<T1> &l1 = *_f.l1;
        if (std::holds_alternative<typename List<T1>::Nil>(l1.v())) {
          if (std::holds_alternative<typename List<T2>::Nil>(l2.v())) {
            _result = Monad0::template ret<
                Monad_res, std::pair<List<std::pair<T1, T2>>, List<T2>>>(
                std::make_pair(List<std::pair<crane::obj, crane::obj>>::nil(),
                               List<crane::obj>::nil()));
          } else {
            _result = Monad0::template ret<
                Monad_res, std::pair<List<std::pair<T1, T2>>, List<T2>>>(
                std::make_pair(List<std::pair<crane::obj, crane::obj>>::nil(),
                               l2));
          }
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l1.v());
          const List<T1> &a1_value = *a1;
          if (std::holds_alternative<typename List<T2>::Nil>(l2.v())) {
            _result = res<std::pair<List<std::pair<T1, T2>>, List<T2>>>::err();
          } else {
            const auto &[a00, a10] = std::get<typename List<T2>::Cons>(l2.v());
            const List<T2> &a10_value = *a10;
            _stack.emplace_back(_Resume_Cons{
                [=](std::pair<List<std::pair<T1, T2>>, List<T2>> x0) {
                  const auto &[l, rest] = x0;
                  return Monad0::template ret<
                      Monad_res, std::pair<List<std::pair<T1, T2>>, List<T2>>>(
                      std::make_pair(List<std::pair<T1, T2>>::cons(
                                         std::make_pair(a0, a00), l),
                                     rest));
                }});
            _stack.emplace_back(_Enter{crane_raw(a10), crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result =
            Monad0::template bind<Monad_res,
                                  std::pair<List<std::pair<T1, T2>>, List<T2>>,
                                  std::pair<List<std::pair<T1, T2>>, List<T2>>>(
                std::move(_result), std::move(_f._s0));
      }
    }
    return _result;
  }

  static bool check(std::monostate _x);
};

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Monad _tcI0, typename T2, typename T3, typename F1>
  requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F1 &, T2 &>
typename _tcI0::template m<T3> Monad0::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

#endif // INCLUDED_LOOPIFY_FRAME_LAMBDA_TYPE
