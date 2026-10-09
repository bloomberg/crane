#ifndef INCLUDED_COINDUCTIVE_TAKE_OVERFLOW
#define INCLUDED_COINDUCTIVE_TAKE_OVERFLOW

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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }
};

struct CoinductiveTakeOverflow {
  /// Taking a long prefix of a lazily forced stream.  Two Cons constructors
  /// are in play -- this stream's and list's -- and the loopified take
  /// writes into the tail field of the latter, so the constructor field names
  /// have to stay told apart by their owning inductive.
  template <typename A> struct stream {
    // TYPES
    template <typename CraneS0 = stream<A>> struct Cons_ {
      A a0;
      CraneS0 a1;
    };

    using Cons = Cons_<>;
    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    stream() {}

    explicit stream(Cons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    template <typename CraneU>
    stream(const stream<CraneU> &_other)
        : lazy_v_(crane::lazy<variant_t>::converted_from(
              _other.lazy_cell(), [=]() -> variant_t {
                const auto &[a0, a1] =
                    std::get<typename stream<CraneU>::Cons>(_other.v());
                return Cons{
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

    static stream<A> cons(A a0, stream<A> a1) {
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

  static stream<uint64_t> from(uint64_t n);

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
      const auto &[a0, a1] = std::get<typename stream<T1>::Cons>(s.v());
      _result = stream<T2>::lazy_([=]() -> typename stream<T2>::Cons {
        return {f(a0), smap<T1, T2>(f, a1)};
      });
    }
    return _result;
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
        uint64_t k = _loop_n - 1;
        const auto &[a0, a1] = std::get<typename stream<T1>::Cons>(_loop_s.v());
        auto _cell = typename List<T1>::Cons(a0, nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_s = a1;
        _loop_n = k;
        continue;
      }
    }
    return std::move(*_root);
  }

  static inline const uint64_t total =
      take<uint64_t>(
          UINT64_C(50000),
          smap<uint64_t, uint64_t>([](uint64_t n) { return (n * UINT64_C(2)); },
                                   from(UINT64_C(0))))
          .template fold_left<uint64_t>(
              [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                return (_x0 + _x1);
              },
              UINT64_C(0));
};

#endif // INCLUDED_COINDUCTIVE_TAKE_OVERFLOW
