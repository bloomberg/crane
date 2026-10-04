#ifndef INCLUDED_LOOPIFY_COIND_COLIST
#define INCLUDED_LOOPIFY_COIND_COLIST

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
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
};

struct LoopifyCoindColist {
  template <typename A> struct colist {
    // TYPES
    struct Conil {};

    template <typename CraneS0 = colist<A>> struct Cocons_ {
      A a0;
      CraneS0 a1;
    };

    using Cocons = Cocons_<>;
    using variant_t = std::variant<Conil, Cocons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    colist() {}

    explicit colist(Conil _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(Cocons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    template <typename CraneU>
    colist(const colist<CraneU> &_other)
        : lazy_v_(crane::lazy<variant_t>::converted_from(
              _other.lazy_cell(), [=]() -> variant_t {
                if (std::holds_alternative<typename colist<CraneU>::Conil>(
                        _other.v())) {
                  return Conil{};
                } else {
                  const auto &[a0, a1] =
                      std::get<typename colist<CraneU>::Cocons>(_other.v());
                  return Cocons{
                      [&]() -> A {
                        if constexpr (crane_convertible<A, const CraneU &>) {
                          return crane_convert<A>(a0);
                        } else {
                          throw std::logic_error(
                              "unreachable: inactive constructor field at this "
                              "instantiation");
                        }
                      }(),
                      crane_convert<colist<A>>(a1)};
                }
              })) {}

    explicit colist(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static colist<A> conil() {
      return colist<A>(
          crane::lazy<variant_t>(std::in_place, std::in_place_index<0>));
    }

    static colist<A> cocons(A a0, colist<A> a1) {
      return colist<A>(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<1>, std::move(a0), std::move(a1)));
    }

    explicit colist(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static colist<A> lazy_(F &&thunk) {
      return colist<A>(
          crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  template <typename T1, typename T2>
  static colist<T2>
  comap(std::type_identity_t<crane::fn<T2(T1)>> f,
        colist<T1> l) { /// CraneEnter: captures varying parameters for each
                        /// recursive call.

    struct CraneEnter {
      colist<T1> l;
    };

    using CraneFrame = std::variant<CraneEnter>;
    colist<T2> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{std::move(l)});
    /// Loopified comap: CraneEnter.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<CraneEnter>(_frame));
      colist<T1> l = std::move(_f.l);
      if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
        _result = colist<T2>::conil();
      } else {
        const auto &[a0, a1] = std::get<typename colist<T1>::Cocons>(l.v());
        _result = colist<T2>::lazy_([=]() -> colist<T2> {
          return colist<T2>::cocons(f(a0), comap<T1, T2>(f, a1));
        });
      }
    }
    return _result;
  }

  template <typename T1>
  static colist<T1>
  cotake(uint64_t n, colist<T1> l) { /// CraneEnter: captures varying parameters
                                     /// for each recursive call.

    struct CraneEnter {
      colist<T1> l;
      uint64_t n;
    };

    using CraneFrame = std::variant<CraneEnter>;
    colist<T1> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{std::move(l), n});
    /// Loopified cotake: CraneEnter.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<CraneEnter>(_frame));
      colist<T1> l = std::move(_f.l);
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = colist<T1>::conil();
      } else {
        uint64_t n_ = n - 1;
        if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
          _result = colist<T1>::conil();
        } else {
          const auto &[a0, a1] = std::get<typename colist<T1>::Cocons>(l.v());
          _result = colist<T1>::lazy_([=]() -> colist<T1> {
            return colist<T1>::cocons(a0, cotake<T1>(n_, a1));
          });
        }
      }
    }
    return _result;
  }

  template <typename T1>
  static colist<T1>
  from_list(const List<T1> &l) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

    struct CraneEnter {
      const List<T1> *l;
    };

    using CraneFrame = std::variant<CraneEnter>;
    colist<T1> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified from_list: CraneEnter.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<T1> &l = *_f.l;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        _result = colist<T1>::conil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        const List<T1> &a1_value = *a1;
        _result = colist<T1>::lazy_([=]() -> colist<T1> {
          return colist<T1>::cocons(a0, from_list<T1>(a1_value));
        });
      }
    }
    return _result;
  }

  template <typename T1> static List<T1> to_list(uint64_t fuel, colist<T1> l) {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> *_write = &_head;
    colist<T1> _loop_l = std::move(l);
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        *_write = std::make_shared<List<T1>>(List<T1>::nil());
        break;
      } else {
        uint64_t f = _loop_fuel - 1;
        if (std::holds_alternative<typename colist<T1>::Conil>(_loop_l.v())) {
          *_write = std::make_shared<List<T1>>(List<T1>::nil());
          break;
        } else {
          const auto &[a0, a1] =
              std::get<typename colist<T1>::Cocons>(_loop_l.v());
          auto _cell =
              std::make_shared<List<T1>>(typename List<T1>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).l;
          _loop_l = a1;
          _loop_fuel = f;
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  static inline const List<uint64_t> test_comap = to_list<uint64_t>(
      UINT64_C(5),
      comap<uint64_t, uint64_t>(
          [](uint64_t n) { return (n * UINT64_C(2)); },
          from_list<uint64_t>(List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(
                  UINT64_C(2),
                  List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))))));

  static inline const List<uint64_t> test_cotake = to_list<uint64_t>(
      UINT64_C(10),
      cotake<uint64_t>(
          UINT64_C(2),
          from_list<uint64_t>(List<uint64_t>::cons(
              UINT64_C(10),
              List<uint64_t>::cons(
                  UINT64_C(20), List<uint64_t>::cons(
                                    UINT64_C(30), List<uint64_t>::nil()))))));
};

#endif // INCLUDED_LOOPIFY_COIND_COLIST
