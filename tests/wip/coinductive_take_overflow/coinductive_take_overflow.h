#ifndef INCLUDED_COINDUCTIVE_TAKE_OVERFLOW
#define INCLUDED_COINDUCTIVE_TAKE_OVERFLOW

#include "crane_fn.h"
#include "lazy.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>) {
                          return crane_any_cast<A>(a);
                        } else {
                          return A(a);
                        }
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
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
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
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
  /// Loopification does not reach a fixpoint whose scrutinee is a lazily
  /// forced coinductive value, so taking a long prefix of a stream overflows
  /// the stack even with Set Crane Loopify.
  template <typename A> struct stream {
    // TYPES
    struct Cons {
      A a0;
      std::shared_ptr<stream<A>> a1;
    };

    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    explicit stream(Cons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream<A> cons(A a0, const stream<A> &a1) {
      return stream<A>(Cons{std::move(a0), std::make_shared<stream<A>>(a1)});
    }

    static stream<A> lazy_(std::function<stream<A>()> thunk) {
      return stream<A>(std::function<variant_t()>([=]() mutable -> variant_t {
        stream<A> _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }
  };

  static stream<uint64_t> from(uint64_t n);

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static stream<T2> smap(F0 &&f, stream<T1> s) {
    const auto &[a0, a1] = std::get<typename stream<T1>::Cons>(s.v());
    return stream<T2>::lazy_([=]() mutable -> stream<T2> {
      return stream<T2>::cons(f(a0), smap<T1, T2>(f, *a1));
    });
  }

  template <typename T1> static List<T1> take(uint64_t n, stream<T1> s) {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> *_write = &_head;
    stream<T1> _loop_s = std::move(s);
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        *_write = std::make_shared<List<T1>>(List<T1>::nil());
        break;
      } else {
        uint64_t k = _loop_n - 1;
        const auto &[a0, a1] = std::get<typename stream<T1>::Cons>(_loop_s.v());
        auto _cell =
            std::make_shared<List<T1>>(typename List<T1>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).a1;
        _loop_s = *a1;
        _loop_n = k;
        continue;
      }
    }
    return std::move(*_head);
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
