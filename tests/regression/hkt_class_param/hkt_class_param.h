#ifndef INCLUDED_HKT_CLASS_PARAM
#define INCLUDED_HKT_CLASS_PARAM

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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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
};

/// A type class parameterised over a type {i constructor} (C : Type -> Type).
/// Crane emits the instance's methods against the shared List type but
/// erases the element type, producing List<std::any> parameters where
/// List<Nat> is required, which corrupts the mapped List type itself.
template <typename I>
concept Container = requires {
  typename I::template C<crane::obj>;
  {
    I::template empty<crane::obj>()
  } -> std::convertible_to<typename I::template C<crane::obj>>;
  {
    I::template insert<crane::obj>(
        std::declval<crane::obj>(),
        std::declval<typename I::template C<crane::obj>>())
  } -> std::convertible_to<typename I::template C<crane::obj>>;
  {
    I::template toList<crane::obj>(
        std::declval<typename I::template C<crane::obj>>())
  } -> std::convertible_to<List<crane::obj>>;
};

struct HktClassParam {
  template <Container _tcI0, typename T2>
  static typename _tcI0::template C<T2> empty() {
    return _tcI0::template empty<T2>();
  }

  template <Container _tcI0, typename T2>
  static typename _tcI0::template C<T2>
  insert(const T2 &x, typename _tcI0::template C<T2> x0) {
    return _tcI0::template insert<T2>(x, std::move(x0));
  }

  template <Container _tcI0, typename T2>
  static List<T2> toList(typename _tcI0::template C<T2> x) {
    return _tcI0::template toList<T2>(std::move(x));
  }

  struct ListContainer {
    template <typename CraneA0> using C = List<CraneA0>;

    template <typename CraneA0> static List<CraneA0> empty() {
      return List<CraneA0>::nil();
    }

    template <typename CraneA0>
    static List<CraneA0> insert(CraneA0 x, List<CraneA0> xs) {
      return List<CraneA0>::cons(std::move(x), std::move(xs));
    }

    template <typename CraneA0> static List<CraneA0> toList(List<CraneA0> xs) {
      return xs;
    }
  };

  static_assert(Container<ListContainer>);

  template <Container _tcI0>
  static typename _tcI0::template C<uint64_t> build(const List<uint64_t> &l) {
    return l.template fold_right<typename _tcI0::template C<uint64_t>>(
        [](uint64_t n, typename _tcI0::template C<uint64_t> acc) {
          return insert<_tcI0, uint64_t>(n, acc);
        },
        empty<_tcI0, uint64_t>());
  }

  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_HKT_CLASS_PARAM
