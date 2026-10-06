#ifndef INCLUDED_HK_CARRIER_ALIAS_APPLIED_AS_TYPE
#define INCLUDED_HK_CARRIER_ALIAS_APPLIED_AS_TYPE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
struct TFunctor_list;
template <typename T, typename Body> struct two;
template <typename T, typename Body> struct modul;

struct HkCarrierAliasAppliedAsType {
  static modul<Nat, List<Nat>> run(const modul<Nat, List<Nat>> &m);
};

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
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
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
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

template <typename I>
concept TFunctor = requires {
  typename I::template T<crane::obj>;
  {
    I::template tfmap<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<typename I::template T<crane::obj>>())
  } -> std::convertible_to<typename I::template T<crane::obj>>;
};

template <TFunctor _tcI0, typename T2, typename T3, typename F0>
typename _tcI0::template T<T3> tfmap(F0 &&f, typename _tcI0::template T<T2> x) {
  return _tcI0::template tfmap<T2, T3>(f, std::move(x));
}

struct TFunctor_list {
  template <typename CraneA0> using T = List<CraneA0>;

  template <typename CraneA0, typename CraneA1>
  static List<CraneA1> tfmap(crane::fn<CraneA1(CraneA0)> a0, List<CraneA0> a1) {
    return a1.template map<CraneA1>(std::move(a0));
  }
};

static_assert(TFunctor<TFunctor_list>);

template <TFunctor _tcI0> struct TFunctor_list_of {
  template <typename CraneA0>
  using T = List<typename _tcI0::template T<CraneA0>>;

  template <typename CraneA0, typename CraneA1>
  static List<typename _tcI0::template T<CraneA1>>
  tfmap(crane::fn<CraneA1(CraneA0)> f,
        List<typename _tcI0::template T<CraneA0>> l) {
    return l.template map<typename _tcI0::template T<CraneA1>>(
        [=, f = std::move(f)](typename _tcI0::template T<CraneA0> a0) {
          return _tcI0::template tfmap<CraneA0, CraneA1>(f, a0);
        });
  }
};

template <typename T, typename Body> struct two {
  T t_head;
  Body t_body;

  // ACCESSORS
  template <typename CraneU0, typename CraneU1>
  operator two<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const T &>) {
                return crane_convert<CraneU0>(t_head);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const Body &>) {
                return crane_convert<CraneU1>(t_body);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }
};

template <TFunctor _tcI0> struct TFunctor_two {
  template <typename CraneA0>
  using T = two<CraneA0, typename _tcI0::template T<CraneA0>>;

  template <typename CraneA0, typename CraneA1>
  static two<CraneA1, typename _tcI0::template T<CraneA1>>
  tfmap(crane::fn<CraneA1(CraneA0)> f,
        two<CraneA0, typename _tcI0::template T<CraneA0>> p) {
    return two<CraneA1, typename _tcI0::template T<CraneA1>>{
        f(p.t_head), _tcI0::template tfmap<CraneA0, CraneA1>(f, p.t_body)};
  }
};

template <typename T, typename Body> struct modul {
  List<two<T, Body>> m_items;

  // ACCESSORS
  template <typename CraneU0, typename CraneU1>
  operator modul<CraneU0, CraneU1>() const {
    return {crane_convert<List<two<CraneU0, CraneU1>>>(m_items)};
  }
};

template <TFunctor _tcI0, TFunctor _tcI1> struct TFunctor_modul {
  template <typename CraneA0>
  using T = modul<CraneA0, typename _tcI0::template T<CraneA0>>;

  template <typename CraneA0, typename CraneA1>
  static modul<CraneA1, typename _tcI0::template T<CraneA1>>
  tfmap(crane::fn<CraneA1(CraneA0)> f,
        modul<CraneA0, typename _tcI0::template T<CraneA0>> m) {
    return modul<CraneA1, typename _tcI0::template T<CraneA1>>{
        TFunctor_list_of<_tcI1>::template tfmap<CraneA0, CraneA1>(
            std::move(f), std::move(m).m_items)};
  }
};

#endif // INCLUDED_HK_CARRIER_ALIAS_APPLIED_AS_TYPE
