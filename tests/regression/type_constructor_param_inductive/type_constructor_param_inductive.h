#ifndef INCLUDED_TYPE_CONSTRUCTOR_PARAM_INDUCTIVE
#define INCLUDED_TYPE_CONSTRUCTOR_PARAM_INDUCTIVE

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
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
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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

  uint64_t length() const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_length_in_Cons {};

    using _frame = std::variant<_call, _after_length_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_Cons>(_popped));
        _stack.pop_back();
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

struct TypeConstructorParamInductive {
  /// An inductive parameterised by a type {e constructor} emits a template
  /// template parameter that its instantiations do not satisfy.
  template <typename F, typename A> struct wrapped {
    // TYPES
    struct Wrap {
      crane::rebind_t<F, A> a0;
    };

    struct Pair2 {
      crane::rebind_t<F, A> a0;
      crane::rebind_t<F, A> a1;
    };

    using variant_t = std::variant<Wrap, Pair2>;
    using crane_family_tag = void;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    wrapped() {}

    explicit wrapped(Wrap _v) : v_(std::move(_v)) {}

    explicit wrapped(Pair2 _v) : v_(std::move(_v)) {}

    template <typename CraneU0, typename CraneU1>
    wrapped(const wrapped<CraneU0, CraneU1> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename wrapped<CraneU0,
                                                        CraneU1>::Wrap>(
                    _other.v())) {
              const auto &[a0] = std::get<
                  typename wrapped<CraneU0, CraneU1>::Wrap>(_other.v());
              return Wrap{[&]() -> F {
                if constexpr (crane_convertible<F, const CraneU0 &>) {
                  return crane_convert<F>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              const auto &[a0, a1] =
                  std::get<typename wrapped<CraneU0, CraneU1>::Pair2>(
                      _other.v());
              return Pair2{
                  [&]() -> F {
                    if constexpr (crane_convertible<F, const CraneU0 &>) {
                      return crane_convert<F>(a0);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  [&]() -> F {
                    if constexpr (crane_convertible<F, const CraneU0 &>) {
                      return crane_convert<F>(a1);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }()};
            }
          }()) {}

    static wrapped<F, A> wrap(crane::rebind_t<F, A> a0) {
      return wrapped<F, A>(Wrap{std::move(a0)});
    }

    static wrapped<F, A> pair2(crane::rebind_t<F, A> a0,
                               crane::rebind_t<F, A> a1) {
      return wrapped<F, A>(Pair2{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, typename F0, typename F1>
    requires std::is_invocable_r_v<T3, F0 &, const crane::rebind_t<T1, T2> &> &&
             std::is_invocable_r_v<T3, F1 &, const crane::rebind_t<T1, T2> &,
                                   const crane::rebind_t<T1, T2> &>
  static T3 wrapped_rect(F0 &&f, F1 &&f0, const wrapped<T1, T2> &w) {
    if (std::holds_alternative<typename wrapped<T1, T2>::Wrap>(w.v())) {
      const auto &[a0] = std::get<typename wrapped<T1, T2>::Wrap>(w.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename wrapped<T1, T2>::Pair2>(w.v());
      return f0(a0, a1);
    }
  }

  template <typename T1, typename T2, typename T3, typename F0, typename F1>
  static T3 wrapped_rec(F0 &&f, F1 &&f0, const wrapped<T1, T2> &w) {
    return wrapped_rect<T1, T2, T3>(f, f0, w);
  }

  static uint64_t size_list(const wrapped<List<crane::obj>, uint64_t> &w);
  static uint64_t
  size_opt(const wrapped<std::optional<crane::obj>, uint64_t> &w);
  static inline const uint64_t total = (((size_list(wrapped<List<crane::obj>,
                                                            uint64_t>::wrap(List<
                                              uint64_t>::cons(
                                              UINT64_C(1),
                                              List<uint64_t>::cons(
                                                  UINT64_C(2),
                                                  List<uint64_t>::cons(
                                                      UINT64_C(3),
                                                      List<uint64_t>::nil()))))) +
                                          size_list(wrapped<List<crane::obj>,
                                                            uint64_t>::pair2(
                                              List<uint64_t>::cons(
                                                  UINT64_C(1),
                                                  List<uint64_t>::nil()),
                                              List<uint64_t>::cons(
                                                  UINT64_C(2),
                                                  List<uint64_t>::cons(
                                                      UINT64_C(3),
                                                      List<uint64_t>::nil()))))) +
                                         size_opt(
                                             wrapped<std::optional<crane::obj>,
                                                     uint64_t>::wrap(
                                                 std::make_optional<uint64_t>(
                                                     UINT64_C(1))))) +
                                        size_opt(
                                            wrapped<std::optional<crane::obj>,
                                                    uint64_t>::pair2(
                                                std::make_optional<uint64_t>(
                                                    UINT64_C(1)),
                                                std::optional<uint64_t>())));
};

#endif // INCLUDED_TYPE_CONSTRUCTOR_PARAM_INDUCTIVE
