#ifndef INCLUDED_COIND_GUARD
#define INCLUDED_COIND_GUARD

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <any>
#include <atomic>
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
};

struct CoindGuard {
  template <typename A> struct Stream {
    // TYPES
    template <typename _S0 = Stream<A>> struct Cons_ {
      A a0;
      _S0 a1;
    };

    using Cons = Cons_<>;
    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    Stream() {}

    explicit Stream(Cons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    template <typename _U>
    Stream(const Stream<_U> &_other)
        : lazy_v_(crane::lazy<variant_t>::converted_from(
              _other.lazy_cell(), [=]() -> variant_t {
                const auto &[a0, a1] =
                    std::get<typename Stream<_U>::Cons>(_other.v());
                return Cons{[&]() -> A {
                              if constexpr (crane_convertible<A, const _U &>) {
                                return crane_convert<A>(a0);
                              } else {
                                throw std::logic_error(
                                    "unreachable: inactive constructor field "
                                    "at this instantiation");
                              }
                            }(),
                            crane_convert<Stream<A>>(a1)};
              })) {}

    explicit Stream(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static Stream<A> cons(A a0, Stream<A> a1) {
      return Stream<A>(Cons{std::move(a0), std::move(a1)});
    }

    explicit Stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static Stream<A> lazy_(F &&thunk) {
      return Stream<A>(
          crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  template <typename T1> static T1 hd(Stream<T1> s) {
    const auto &[a0, a1] = std::get<typename Stream<T1>::Cons>(s.v());
    return a0;
  }

  template <typename T1> static Stream<T1> tl(Stream<T1> s) {
    const auto &[a0, a1] = std::get<typename Stream<T1>::Cons>(s.v());
    return a1;
  }

  template <typename T1>
  static Stream<T1> iterate(std::type_identity_t<crane::fn<T1(T1)>> f,
                            const T1 &x) {
    return Stream<T1>::lazy_([=]() -> Stream<T1> {
      return Stream<T1>::cons(x, iterate<T1>(f, f(x)));
    });
  }

  template <typename T1, typename T2, typename T3>
  static Stream<T3> zipWith(std::type_identity_t<crane::fn<T3(T1, T2)>> f,
                            Stream<T1> s1, Stream<T2> s2) {
    return Stream<T3>::lazy_([=]() -> Stream<T3> {
      return Stream<T3>::cons(f(hd<T1>(s1), hd<T2>(s2)),
                              zipWith<T1, T2, T3>(f, tl<T1>(s1), tl<T2>(s2)));
    });
  }

  template <typename T1, typename T2>
  static Stream<T2> smap(std::type_identity_t<crane::fn<T2(T1)>> f,
                         Stream<T1> s) {
    return Stream<T2>::lazy_([=]() -> Stream<T2> {
      return Stream<T2>::cons(f(hd<T1>(s)), smap<T1, T2>(f, tl<T1>(s)));
    });
  }

  template <typename T1, typename T2>
  static Stream<T1>
  unfold(std::type_identity_t<crane::fn<std::pair<T1, T2>(T2)>> f,
         const T2 &seed) {
    auto [a, s_] = f(seed);
    return Stream<T1>::lazy_([=]() -> Stream<T1> {
      return Stream<T1>::cons(a, unfold<T1, T2>(f, s_));
    });
  }

  template <typename T1> static List<T1> take(uint64_t n, Stream<T1> s) {
    if (n <= 0) {
      return List<T1>::nil();
    } else {
      uint64_t n_ = n - 1;
      return List<T1>::cons(hd<T1>(s), take<T1>(n_, tl<T1>(s)));
    }
  }

  static inline const Stream<uint64_t> nats =
      iterate<uint64_t>([](uint64_t x) { return (x + 1); }, UINT64_C(0));
  static inline const Stream<uint64_t> evens = smap<uint64_t, uint64_t>(
      [](uint64_t n) { return (n * UINT64_C(2)); }, nats);
  static inline const Stream<uint64_t> fibs =
      unfold<uint64_t, std::pair<uint64_t, uint64_t>>(
          [](std::pair<uint64_t, uint64_t> pat) {
            const auto &[a, b] = pat;
            return std::make_pair(a, std::make_pair(b, (a + b)));
          },
          std::make_pair(UINT64_C(0), UINT64_C(1)));
  static inline const Stream<uint64_t> sum_stream =
      zipWith<uint64_t, uint64_t, uint64_t>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          nats, evens);
  static inline const List<uint64_t> test_nats_5 =
      take<uint64_t>(UINT64_C(5), nats);
  static inline const List<uint64_t> test_evens_5 =
      take<uint64_t>(UINT64_C(5), evens);
  static inline const List<uint64_t> test_fibs_8 =
      take<uint64_t>(UINT64_C(8), fibs);
  static inline const List<uint64_t> test_sum_5 =
      take<uint64_t>(UINT64_C(5), sum_stream);
  static inline const uint64_t test_iterate_hd = hd<uint64_t>(nats);
};

#endif // INCLUDED_COIND_GUARD
