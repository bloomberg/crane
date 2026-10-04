#ifndef INCLUDED_STREAM
#define INCLUDED_STREAM

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <stdexcept>
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
};

template <typename A> struct Stream {
  // TYPES
  template <typename CraneS0 = Stream<A>> struct Scons_ {
    A x;
    CraneS0 xs;
  };

  using Scons = Scons_<>;
  using variant_t = std::variant<Scons>;

private:
  // DATA
  crane::lazy<variant_t> lazy_v_;

public:
  // CREATORS
  Stream() {}

  explicit Stream(Scons _v)
      : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  template <typename CraneU>
  Stream(const Stream<CraneU> &_other)
      : lazy_v_(crane::lazy<variant_t>::converted_from(
            _other.lazy_cell(), [=]() -> variant_t {
              const auto &[x, xs] =
                  std::get<typename Stream<CraneU>::Scons>(_other.v());
              return Scons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(x);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  crane_convert<Stream<A>>(xs)};
            })) {}

  explicit Stream(crane::fn<variant_t()> _thunk)
      : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  static Stream<A> scons(A x, Stream<A> xs) {
    return Stream<A>(crane::lazy<variant_t>(
        std::in_place, std::in_place_index<0>, std::move(x), std::move(xs)));
  }

  explicit Stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

  template <typename F> static Stream<A> lazy_(F &&thunk) {
    return Stream<A>(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
  }

  // ACCESSORS
  const variant_t &v() const { return lazy_v_.force(); }

  const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }

  Stream<A> interleave(Stream<A> sb) const {
    const auto &[a0, a1] = std::get<typename Stream<A>::Scons>(this->v());
    return Stream<A>::lazy_(
        [=]() -> Stream<A> { return Stream<A>::scons(a0, sb.interleave(a1)); });
  }

  template <typename T1> static List<T1> take(const Nat &n, Stream<T1> s) {
    if (std::holds_alternative<typename Nat::O>(n.v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0] = std::get<typename Nat::S>(n.v());
      const auto &[a00, a10] = std::get<typename Stream<T1>::Scons>(s.v());
      return List<T1>::cons(a00, take<T1>(*a0, a10));
    }
  }

  template <typename T1> static Stream<T1> repeat(const T1 &x) {
    return Stream<T1>::lazy_(
        [=]() -> Stream<T1> { return Stream<T1>::scons(x, repeat<T1>(x)); });
  }

  static Stream<Nat> nats_from(const Nat &n) {
    return Stream<Nat>::lazy_([=]() -> Stream<Nat> {
      return Stream<Nat>::scons(n, nats_from(Nat::s(n)));
    });
  }

  static const Stream<Nat> &ones() {
    static const Stream<Nat> v = repeat<Nat>(Nat::s(Nat::o()));
    return v;
  }

  static const List<Nat> &first_five_nats() {
    static const List<Nat> v = take<Nat>(
        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))), nats_from(Nat::o()));
    return v;
  }

  static const List<Nat> &first_five_ones() {
    static const List<Nat> v =
        take<Nat>(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))), ones());
    return v;
  }

  static const List<Nat> &interleaved() {
    static const List<Nat> v = take<Nat>(
        Nat::s(
            Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))),
        nats_from(Nat::o()).interleave(repeat<Nat>(
            Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))))));
    return v;
  }
};

#endif // INCLUDED_STREAM
