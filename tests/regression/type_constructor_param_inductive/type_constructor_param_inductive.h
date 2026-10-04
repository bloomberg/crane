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
            if (std::holds_alternative<
                    typename wrapped<CraneU0, CraneU1>::Wrap>(_other.v())) {
              const auto &[a0] =
                  std::get<typename wrapped<CraneU0, CraneU1>::Wrap>(
                      _other.v());
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
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  [&]() -> F {
                    if constexpr (crane_convertible<F, const CraneU0 &>) {
                      return crane_convert<F>(a1);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
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
    requires std::is_invocable_r_v<T3, F0 &, crane::rebind_t<T1, T2> &> &&
             std::is_invocable_r_v<T3, F1 &, crane::rebind_t<T1, T2> &,
                                   crane::rebind_t<T1, T2> &>
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
    requires std::is_invocable_r_v<T3, F0 &, crane::rebind_t<T1, T2> &> &&
             std::is_invocable_r_v<T3, F1 &, crane::rebind_t<T1, T2> &,
                                   crane::rebind_t<T1, T2> &>
  static T3 wrapped_rec(F0 &&f, F1 &&f0, const wrapped<T1, T2> &w) {
    if (std::holds_alternative<typename wrapped<T1, T2>::Wrap>(w.v())) {
      const auto &[a0] = std::get<typename wrapped<T1, T2>::Wrap>(w.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename wrapped<T1, T2>::Pair2>(w.v());
      return f0(a0, a1);
    }
  }

  static uint64_t size_list(const wrapped<List<crane::obj>, uint64_t> &w);
  static uint64_t
  size_opt(const wrapped<std::optional<crane::obj>, uint64_t> &w);

  static inline const uint64_t total =
      (((size_list(
             wrapped<List<crane::obj>, uint64_t>::wrap(List<uint64_t>::cons(
                 UINT64_C(1),
                 List<uint64_t>::cons(
                     UINT64_C(2), List<uint64_t>::cons(
                                      UINT64_C(3), List<uint64_t>::nil()))))) +
         size_list(wrapped<List<crane::obj>, uint64_t>::pair2(
             List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()),
             List<uint64_t>::cons(
                 UINT64_C(2),
                 List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))))) +
        size_opt(wrapped<std::optional<crane::obj>, uint64_t>::wrap(
            std::make_optional<uint64_t>(UINT64_C(1))))) +
       size_opt(wrapped<std::optional<crane::obj>, uint64_t>::pair2(
           std::make_optional<uint64_t>(UINT64_C(1)),
           std::optional<uint64_t>())));
};

#endif // INCLUDED_TYPE_CONSTRUCTOR_PARAM_INDUCTIVE
