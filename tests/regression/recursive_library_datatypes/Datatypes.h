#ifndef INCLUDED_DATATYPES
#define INCLUDED_DATATYPES

#include "crane_fn.h"
#include "fn.h"
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

namespace Datatypes {
struct Empty_set;
enum class Reflect;
template <typename A, typename B> struct Sum;
template <typename A, typename E> struct Result;
template <typename A> struct List;
enum class Comparison;
enum class CompareSpecT;

struct Empty_set {
  Empty_set() = delete;

  crane::obj Empty_set_rect() const { throw std::logic_error("absurd case"); }

  template <typename T1> T1 Empty_set_rec() const {
    return this->Empty_set_rect();
  }
};

template <typename T1> T1 unit_rect(T1 f) {
  {
    return f;
  }
}

template <typename T1> T1 unit_rec(T1 f) { return unit_rect<T1>(std::move(f)); }

template <typename T1> T1 bool_rect(T1 f, T1 f0, bool b) {
  if (b) {
    return f;
  } else {
    return f0;
  }
}

template <typename T1> T1 bool_rec(T1 f, T1 f0, bool b) {
  return bool_rect<T1>(std::move(f), std::move(f0), b);
}

enum class Reflect { REFLECTT, REFLECTF };

template <typename T1>
T1 reflect_rect(const T1 &f, const T1 &f0, bool, Reflect r) {
  switch (r) {
  case Reflect::REFLECTT: {
    return f;
  }
  case Reflect::REFLECTF: {
    return f0;
  }
  default:
    std::unreachable();
  }
}

template <typename T1>
T1 reflect_rec(const T1 &f, const T1 &f0, bool _x, Reflect r) {
  return reflect_rect<T1>(f, f0, _x, r);
}

bool implb(bool b1, bool b2);
bool xorb(bool b1, bool b2);

template <typename T1> T1 eq_true_rect(T1 f, bool) { return f; }

template <typename T1> T1 eq_true_rec(T1 f, bool _x) {
  return eq_true_rect<T1>(std::move(f), _x);
}

template <typename T1> T1 eq_true_rec_r(bool, T1 h) { return h; }

template <typename T1> T1 eq_true_rect_r(bool _x, T1 h) {
  return eq_true_rec_r<T1>(_x, std::move(h));
}

template <typename T1, typename F1> T1 nat_rect(T1 f, F1 &&f0, uint64_t n) {
  if (n <= 0) {
    return f;
  } else {
    uint64_t n0 = n - 1;
    return f0(n0, nat_rect<T1>(std::move(f), f0, n0));
  }
}

template <typename T1, typename F1> T1 nat_rec(T1 f, F1 &&f0, uint64_t n) {
  return nat_rect<T1>(std::move(f), f0, n);
}

template <typename T1, typename T2, typename F0>
T2 option_rect(F0 &&f, T2 f0, const std::optional<T1> &o) {
  if (o.has_value()) {
    const T1 &a = *o;
    return f(a);
  } else {
    return f0;
  }
}

template <typename T1, typename T2, typename F0>
T2 option_rec(F0 &&f, T2 f0, const std::optional<T1> &o) {
  return option_rect<T1, T2>(f, std::move(f0), o);
}

template <typename T1, typename T2, typename F0>
std::optional<T2> option_map(F0 &&f, const std::optional<T1> &o) {
  if (o.has_value()) {
    const T1 &a = *o;
    return std::make_optional<T2>(f(a));
  } else {
    return std::optional<T2>();
  }
}

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1>
  Sum(const Sum<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum<CraneU0, CraneU1>::Inl>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inl>(_other.v());
            return Inl{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inr>(_other.v());
            return Inr{[&]() -> B {
              if constexpr (crane_convertible<B, const CraneU1 &>) {
                return crane_convert<B>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const A &> &&
             std::is_invocable_r_v<T1, F1 &, const B &>
  T1 sum_rect(F0 &&f, F1 &&f0) const {
    if (std::holds_alternative<typename Sum<A, B>::Inl>(this->v())) {
      const auto &[a0] = std::get<typename Sum<A, B>::Inl>(this->v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename Sum<A, B>::Inr>(this->v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
  T1 sum_rec(F0 &&f, F1 &&f0) const {
    return this->template sum_rect<T1>(f, f0);
  }
};

template <typename A, typename E> struct Result {
  // TYPES
  struct Ok {
    A a0;
  };

  struct Error {
    E a0;
  };

  using variant_t = std::variant<Ok, Error>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Result() {}

  explicit Result(Ok _v) : v_(std::move(_v)) {}

  explicit Result(Error _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1>
  Result(const Result<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Result<CraneU0, CraneU1>::Ok>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Result<CraneU0, CraneU1>::Ok>(_other.v());
            return Ok{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Result<CraneU0, CraneU1>::Error>(_other.v());
            return Error{[&]() -> E {
              if constexpr (crane_convertible<E, const CraneU1 &>) {
                return crane_convert<E>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Result<A, E> ok(A a0) { return Result<A, E>(Ok{std::move(a0)}); }

  static Result<A, E> error(E a0) { return Result<A, E>(Error{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const A &> &&
             std::is_invocable_r_v<T1, F1 &, const E &>
  T1 result_rect(F0 &&f, F1 &&f0) const {
    if (std::holds_alternative<typename Result<A, E>::Ok>(this->v())) {
      const auto &[a0] = std::get<typename Result<A, E>::Ok>(this->v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename Result<A, E>::Error>(this->v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
  T1 result_rec(F0 &&f, F1 &&f0) const {
    return this->template result_rect<T1>(f, f0);
  }
};

template <typename T1, typename T2, typename T3, typename F0>
T3 prod_rect(F0 &&f, const std::pair<T1, T2> &p) {
  const auto &[a, b] = p;
  return f(a, b);
}

template <typename T1, typename T2, typename T3, typename F0>
T3 prod_rec(F0 &&f, const std::pair<T1, T2> &p) {
  return prod_rect<T1, T2, T3>(f, p);
}

template <typename T1, typename T2, typename T3, typename F0>
  requires std::is_invocable_r_v<T3, F0 &, std::pair<T1, T2>>
T3 curry(F0 &&f, const T1 &x, const T2 &y) {
  return f(std::make_pair(x, y));
}

template <typename T1, typename T2, typename T3, typename F0>
T3 uncurry(F0 &&f, const std::pair<T1, T2> &p) {
  return prod_rect<T1, T2, T3>(f, p);
}

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

  template <typename T1, typename F1> T1 list_rect(T1 f, F1 &&f0) const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of list_rect: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_list_rect_in_Cons {
      A a0;
      std::shared_ptr<List<A>> a1;
    };

    using _frame = std::variant<_call, _after_list_rect_in_Cons>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame _popped = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_list_rect_in_Cons{a0, a1});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_list_rect_in_Cons>(_popped));
        auto a0 = std::move(_f.a0);
        std::shared_ptr<List<A>> a1 = std::move(_f.a1);
        _result = f0(a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1> T1 list_rec(T1 f, F1 &&f0) const {
    return this->template list_rect<T1>(std::move(f), f0);
  }

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
      _frame _popped = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
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
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

  List<A> app(List<A> m) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

enum class Comparison { EQ, LT, GT };

template <typename T1> T1 comparison_rect(T1 f, T1 f0, T1 f1, Comparison c) {
  switch (c) {
  case Comparison::EQ: {
    return f;
  }
  case Comparison::LT: {
    return f0;
  }
  case Comparison::GT: {
    return f1;
  }
  default:
    std::unreachable();
  }
}

template <typename T1> T1 comparison_rec(T1 f, T1 f0, T1 f1, Comparison c) {
  return comparison_rect<T1>(std::move(f), std::move(f0), std::move(f1), c);
}

Comparison CompOpp(Comparison r);
enum class CompareSpecT { COMPEQT, COMPLTT, COMPGTT };

template <typename T1>
T1 CompareSpecT_rect(const T1 &f, const T1 &f0, const T1 &f1, Comparison,
                     CompareSpecT c0) {
  switch (c0) {
  case CompareSpecT::COMPEQT: {
    return f;
  }
  case CompareSpecT::COMPLTT: {
    return f0;
  }
  case CompareSpecT::COMPGTT: {
    return f1;
  }
  default:
    std::unreachable();
  }
}

template <typename T1>
T1 CompareSpecT_rec(const T1 &f, const T1 &f0, const T1 &f1, Comparison _x,
                    CompareSpecT c0) {
  return CompareSpecT_rect<T1>(f, f0, f1, _x, c0);
}

CompareSpecT CompareSpec2Type(Comparison c);
template <typename a = void> using CompSpecT = CompareSpecT;

template <typename T1>
CompSpecT<T1> CompSpec2Type(const T1 &, const T1 &, Comparison x0_) {
  return CompareSpec2Type(x0_);
}

using ID = crane::fn<crane::obj(crane::obj)>;
crane::obj id(crane::obj x);
} // namespace Datatypes

#endif // INCLUDED_DATATYPES
