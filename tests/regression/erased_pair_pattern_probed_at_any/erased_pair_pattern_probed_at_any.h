#ifndef INCLUDED_ERASED_PAIR_PATTERN_PROBED_AT_ANY
#define INCLUDED_ERASED_PAIR_PATTERN_PROBED_AT_ANY

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
struct ident;
template <typename T> struct box;
template <typename T, typename Body> struct pairs;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool ltb(const Nat &m) const { return Nat::s(std::move(*this)).leb(m); }

  bool leb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        return true;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return false;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }
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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ =
          Cons{[&]() -> A {
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
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
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
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> *_write = &_head;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<T1>>(List<T1>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<T1>>(typename List<T1>::Cons(f(a0), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};
template <template <typename> class t>
using TFunctor =
    std::function<t<std::any>(std::function<std::any(std::any)>, t<std::any>)>;

template <template <typename> class T1, typename T2, typename F1,
          typename T3 = std::invoke_result_t<F1 &, T2 &>>
T1<T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor, F1 &&f, T1<T2> x) {
  return crane_container_cast<T1<T3>>(
      tFunctor(crane_erase_fn(f), crane_convert<T1<std::any>>(std::move(x))));
}

List<std::any> TFunctor_list(std::function<std::any(std::any)> x0_,
                             const List<std::any> &x1_);

struct ident {
  Nat i_name;
};

template <typename T> struct box {
  T b_payload;

  // ACCESSORS
  template <typename _U> operator box<_U>() const {
    return {[&]() -> _U {
      if constexpr (crane_convertible<_U, const T &>) {
        return crane_convert<_U>(b_payload);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }
};

box<std::any> TFunctor_box(std::function<std::any(std::any)> f,
                           const box<std::any> &b);

template <typename T, typename Body> struct pairs {
  List<std::pair<ident, T>> p_defs;
  Body p_body;

  // ACCESSORS
  template <typename _U0, typename _U1> operator pairs<_U0, _U1>() const {
    return {crane_convert<List<std::pair<ident, _U0>>>(p_defs), [&]() -> _U1 {
              if constexpr (crane_convertible<_U1, const Body &>) {
                return crane_convert<_U1>(p_body);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }
};

template <template <typename> class T1, typename F1>
pairs<std::any, T1<std::any>>
TFunctor_pairs(std::type_identity_t<TFunctor<T1>> h, F1 &&f,
               const pairs<std::any, T1<std::any>> &m) {
  return pairs<std::any, T1<std::any>>{
      tfmap<List>([](auto &&_ec0,
                     List<std::any> _ec1) { return TFunctor_list(_ec0, _ec1); },
                  [=](std::pair<ident, std::any> pat) mutable {
                    const auto &[id, t] = pat;
                    return std::make_pair(std::any_cast<ident>(id),
                                          std::any(crane_call_erased(f, t)));
                  },
                  m.p_defs),
      tfmap<T1, std::any>(std::move(h), f, m.p_body)};
}

pairs<bool, box<bool>> run(const pairs<Nat, box<Nat>> &m);

#endif // INCLUDED_ERASED_PAIR_PATTERN_PROBED_AT_ANY
