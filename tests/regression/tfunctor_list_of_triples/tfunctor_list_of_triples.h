#ifndef INCLUDED_TFUNCTOR_LIST_OF_TRIPLES
#define INCLUDED_TFUNCTOR_LIST_OF_TRIPLES

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;

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

  bool eqb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return true;
        } else {
          return false;
        }
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

  Nat add(Nat m) const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_root);
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

struct TfunctorListOfTriples {
  template <typename t>
  using TFunctor = crane::fn<t(crane::fn<crane::obj(crane::obj)>, t)>;

  template <typename T1, typename T2, typename T3, typename F1>
  static crane::rebind_t<T1, T3>
  tfmap(std::type_identity_t<TFunctor<T1>> tFunctor, F1 &&f,
        crane::rebind_t<T1, T2> x) {
    return crane_container_cast<crane::rebind_t<T1, T3>>(
        tFunctor(crane_erase_fn(f), crane_convert<T1>(std::move(x))));
  }

  static List<crane::obj> TFunctor_list(crane::fn<crane::obj(crane::obj)> x0_,
                                        const List<crane::obj> &x1_);

  template <typename T1, typename F1>
  static List<T1> TFunctor_list_(std::type_identity_t<TFunctor<T1>> h, F1 &&f,
                                 List<T1> x0_) {
    return std::move(x0_).template map<T1>([=](T1 _x0) -> T1 {
      return tfmap<T1, crane::obj, crane::obj>(h, f, _x0);
    });
  }

  template <typename T> struct phi {
    // DATA
    T t;

    // ACCESSORS
    phi<T> clone() const { return {t}; }

    template <typename CraneU> operator phi<CraneU>() const {
      return {[&]() -> CraneU {
        if constexpr (crane_convertible<CraneU, const T &>) {
          return crane_convert<CraneU>(t);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }

    // CREATORS
    static phi<T> phi0(T t) { return {std::move(t)}; }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const T &>
    T1 phi_rec(F0 &&f) const {
      const auto &[t0] = *this;
      return f(t0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const T &>
    T1 phi_rect(F0 &&f) const {
      const auto &[t0] = *this;
      return f(t0);
    }
  };

  template <typename T> struct metadata {
    // DATA
    T t;

    // ACCESSORS
    metadata<T> clone() const { return {t}; }

    template <typename CraneU> operator metadata<CraneU>() const {
      return {[&]() -> CraneU {
        if constexpr (crane_convertible<CraneU, const T &>) {
          return crane_convert<CraneU>(t);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }

    // CREATORS
    static metadata<T> md(T t) { return {std::move(t)}; }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const T &>
    T1 metadata_rec(F0 &&f) const {
      const auto &[t0] = *this;
      return f(t0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const T &>
    T1 metadata_rect(F0 &&f) const {
      const auto &[t0] = *this;
      return f(t0);
    }
  };

  template <typename T> struct block {
    List<std::pair<std::pair<Nat, phi<T>>, List<metadata<T>>>> blk_phis;

    // ACCESSORS
    template <typename CraneU> operator block<CraneU>() const {
      return {crane_convert<
          List<std::pair<std::pair<Nat, phi<CraneU>>, List<metadata<CraneU>>>>>(
          blk_phis)};
    }
  };

  static phi<crane::obj> TFunctor_phi(crane::fn<crane::obj(crane::obj)> f,
                                      const phi<crane::obj> &p);
  static metadata<crane::obj> TFunctor_md(crane::fn<crane::obj(crane::obj)> f,
                                          const metadata<crane::obj> &p);
  static block<crane::obj> TFunctor_block(crane::fn<crane::obj(crane::obj)> f,
                                          const block<crane::obj> &b);
  static inline const block<Nat> b0 = block<
      Nat>{List<std::pair<std::pair<Nat, phi<Nat>>, List<metadata<Nat>>>>::cons(
      std::make_pair(std::make_pair(Nat::s(Nat::o()),
                                    phi<Nat>::phi0(Nat::s(Nat::s(Nat::o())))),
                     List<metadata<Nat>>::cons(
                         metadata<Nat>::md(
                             Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))),
                         List<metadata<Nat>>::nil())),
      List<std::pair<std::pair<Nat, phi<Nat>>, List<metadata<Nat>>>>::nil())};
  static inline const block<Nat> b1 = tfmap<block<crane::obj>, Nat, Nat>(
      [](auto &&_ec0, block<crane::obj> _ec1) {
        return TFunctor_block(_ec0, _ec1);
      },
      [](const Nat &x) { return Nat::s(x); }, b0);
  static inline const Nat total = []() {
    auto &&_sv = b1.blk_phis;
    if (std::holds_alternative<typename List<
            std::pair<std::pair<Nat, phi<Nat>>, List<metadata<Nat>>>>::Nil>(
            _sv.v())) {
      return Nat::o();
    } else {
      const auto &[a0, a1] = std::get<typename List<
          std::pair<std::pair<Nat, phi<Nat>>, List<metadata<Nat>>>>::Cons>(
          _sv.v());
      const auto &[p0, _x0] = a0;
      const auto &[id, p1] = p0;
      const auto &[t0] = p1;
      return id.add(t0);
    }
  }();
  static inline const bool is_four =
      total.eqb(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))));
};

#endif // INCLUDED_TFUNCTOR_LIST_OF_TRIPLES
