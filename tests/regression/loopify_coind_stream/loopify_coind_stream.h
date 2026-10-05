#ifndef INCLUDED_LOOPIFY_COIND_STREAM
#define INCLUDED_LOOPIFY_COIND_STREAM

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
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

struct LoopifyCoindStream {
  template <typename A> struct stream {
    // TYPES
    template <typename CraneS0 = stream<A>> struct Scons_ {
      A a0;
      CraneS0 a1;
    };

    using Scons = Scons_<>;
    using variant_t = std::variant<Scons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    stream() {}

    explicit stream(Scons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    template <typename CraneU>
    stream(const stream<CraneU> &_other)
        : lazy_v_(crane::lazy<variant_t>::converted_from(
              _other.lazy_cell(), [=]() -> variant_t {
                const auto &[a0, a1] =
                    std::get<typename stream<CraneU>::Scons>(_other.v());
                return Scons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a0);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    crane_convert<stream<A>>(a1)};
              })) {}

    explicit stream(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream<A> scons(A a0, stream<A> a1) {
      return stream<A>(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, std::move(a0), std::move(a1)));
    }

    explicit stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static stream<A> lazy_(F &&thunk) {
      return stream<A>(
          crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  template <typename T1> static T1 hd(const stream<T1> &s) {
    const auto &[a0, a1] = std::get<typename stream<T1>::Scons>(s.v());
    return a0;
  }

  template <typename T1> static stream<T1> tl(const stream<T1> &s) {
    const auto &[a0, a1] = std::get<typename stream<T1>::Scons>(s.v());
    return a1;
  }

  template <typename T1> static List<T1> take(uint64_t n, const stream<T1> &s) {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    stream<T1> _loop_s = s;
    uint64_t _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t n_ = _loop_n - 1;
        auto _cell = typename List<T1>::Cons(hd<T1>(_loop_s), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_s = tl<T1>(_loop_s);
        _loop_n = n_;
        continue;
      }
    }
    return std::move(*_root);
  }

  template <typename T1>
  static stream<T1>
  iterate(const std::type_identity_t<crane::fn<T1(T1)>> &f,
          const T1 &x) { /// CraneEnter: captures varying parameters for each
                         /// recursive call.

    struct CraneEnter {
      T1 x;
    };

    using CraneFrame = std::variant<CraneEnter>;
    stream<T1> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{x});
    /// Loopified iterate: CraneEnter.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const T1 x = std::move(_f.x);
      _result = stream<T1>::lazy_([=]() -> stream<T1> {
        return stream<T1>::scons(x, iterate<T1>(f, f(x)));
      });
    }
    return _result;
  }

  template <typename T1, typename T2>
  static stream<T2>
  smap(const std::type_identity_t<crane::fn<T2(T1)>> &f,
       const stream<T1> &s) { /// CraneEnter: captures varying parameters for
                              /// each recursive call.

    struct CraneEnter {
      stream<T1> s;
    };

    using CraneFrame = std::variant<CraneEnter>;
    stream<T2> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{s});
    /// Loopified smap: CraneEnter.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const stream<T1> &s = _f.s;
      _result = stream<T2>::lazy_([=]() -> stream<T2> {
        return stream<T2>::scons(f(hd<T1>(s)), smap<T1, T2>(f, tl<T1>(s)));
      });
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3>
  static stream<T3>
  zipWith(const std::type_identity_t<crane::fn<T3(T1, T2)>> &f,
          const stream<T1> &s1,
          const stream<T2> &s2) { /// CraneEnter: captures varying parameters
                                  /// for each recursive call.

    struct CraneEnter {
      stream<T2> s2;
      stream<T1> s1;
    };

    using CraneFrame = std::variant<CraneEnter>;
    stream<T3> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{s2, s1});
    /// Loopified zipWith: CraneEnter.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const stream<T2> &s2 = _f.s2;
      const stream<T1> &s1 = _f.s1;
      _result = stream<T3>::lazy_([=]() -> stream<T3> {
        return stream<T3>::scons(
            f(hd<T1>(s1), hd<T2>(s2)),
            zipWith<T1, T2, T3>(f, tl<T1>(s1), tl<T2>(s2)));
      });
    }
    return _result;
  }

  template <typename T1, typename T2>
  static stream<T1>
  unfold(const std::type_identity_t<crane::fn<std::pair<T1, T2>(T2)>> &f,
         const T2 &seed) { /// CraneEnter: captures varying parameters for each
                           /// recursive call.

    struct CraneEnter {
      T2 seed;
    };

    using CraneFrame = std::variant<CraneEnter>;
    stream<T1> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{seed});
    /// Loopified unfold: CraneEnter.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const T2 seed = std::move(_f.seed);
      auto [a, s_] = f(seed);
      _result = stream<T1>::lazy_([=]() -> stream<T1> {
        return stream<T1>::scons(a, unfold<T1, T2>(f, s_));
      });
    }
    return _result;
  }

  static inline const stream<uint64_t> nats =
      iterate<uint64_t>([](uint64_t x) { return (x + 1); }, UINT64_C(0));
  static inline const stream<uint64_t> doubled = smap<uint64_t, uint64_t>(
      [](uint64_t n) { return (n * UINT64_C(2)); }, nats);
  static inline const stream<uint64_t> sum_stream =
      zipWith<uint64_t, uint64_t, uint64_t>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          nats, doubled);
  static inline const stream<uint64_t> fibs =
      unfold<uint64_t, std::pair<uint64_t, uint64_t>>(
          [](std::pair<uint64_t, uint64_t> pat) {
            const auto &[a, b] = pat;
            return std::make_pair(a, std::make_pair(b, (a + b)));
          },
          std::make_pair(UINT64_C(0), UINT64_C(1)));
  static inline const List<uint64_t> test_nats_5 =
      take<uint64_t>(UINT64_C(5), nats);
  static inline const List<uint64_t> test_doubled_5 =
      take<uint64_t>(UINT64_C(5), doubled);
  static inline const List<uint64_t> test_sum_5 =
      take<uint64_t>(UINT64_C(5), sum_stream);
  static inline const List<uint64_t> test_fibs_8 =
      take<uint64_t>(UINT64_C(8), fibs);
};

#endif // INCLUDED_LOOPIFY_COIND_STREAM
