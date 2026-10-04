#ifndef INCLUDED_LOOPIFY_GENERATORS
#define INCLUDED_LOOPIFY_GENERATORS

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
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

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};

/// Consolidated list generator functions.
struct LoopifyGenerators {
  /// cycle n l repeats the list n times: cycle 2 1,2 -> 1,2,1,2.
  static List<uint64_t> cycle(uint64_t n, const List<uint64_t> &l);

  /// iterate f n x applies f repeatedly n times: iterate (+1) 3 5 -> 5,6,7.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static List<uint64_t> iterate(F0 &&f, uint64_t n, uint64_t x) {
    std::shared_ptr<List<uint64_t>> _head{};
    std::shared_ptr<List<uint64_t>> *_write = &_head;
    uint64_t _loop_x = std::move(x);
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        uint64_t m = _loop_n - 1;
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(_loop_x, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_x = f(_loop_x);
        _loop_n = m;
        continue;
      }
    }
    return std::move(*_head);
  }

  /// zip_with f l1 l2 zips with a combining function.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t> zip_with(F0 &&f, const List<uint64_t> &l1,
                                 const List<uint64_t> &l2) {
    std::shared_ptr<List<uint64_t>> _head{};
    std::shared_ptr<List<uint64_t>> *_write = &_head;
    const List<uint64_t> *_loop_l2 = &l2;
    const List<uint64_t> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l2->v())) {
          *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(f(a0, a00), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l2 = crane_raw(a10);
          _loop_l1 = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// zip_longest l1 l2 default zips, using default for missing elements.
  static List<std::pair<uint64_t, uint64_t>>
  zip_longest_aux(const List<uint64_t> &l1, const List<uint64_t> &l2,
                  uint64_t default0, uint64_t fuel);
  static uint64_t len_impl(const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>>
  zip_longest(const List<uint64_t> &l1, const List<uint64_t> &l2,
              uint64_t default0);
  /// build_list n builds tree-like list structure: build_list(4) -> 2,4,2.
  static List<uint64_t> build_list_fuel(uint64_t fuel, uint64_t n);
  static List<uint64_t> build_list(uint64_t n);
  /// take n l returns first n elements.
  static List<uint64_t> take(uint64_t n, const List<uint64_t> &l);
  /// repeat x n creates list with n copies of x.
  static List<uint64_t> repeat(uint64_t x, uint64_t n);

  /// unfold f n init unfolds a list from seed value.
  template <typename F1>
    requires std::is_invocable_r_v<std::pair<uint64_t, uint64_t>, F1 &,
                                   uint64_t &>
  static List<uint64_t> unfold_fuel(uint64_t fuel, F1 &&f, uint64_t n,
                                    uint64_t seed) {
    std::shared_ptr<List<uint64_t>> _head{};
    std::shared_ptr<List<uint64_t>> *_write = &_head;
    uint64_t _loop_seed = std::move(seed);
    uint64_t _loop_n = std::move(n);
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        uint64_t g = _loop_fuel - 1;
        if (_loop_n == UINT64_C(0)) {
          *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
          break;
        } else {
          auto [val, next_seed] = f(_loop_seed);
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(val, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_seed = next_seed;
          _loop_n = ((
              (_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
          _loop_fuel = g;
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename F0>
    requires std::is_invocable_r_v<std::pair<uint64_t, uint64_t>, F0 &,
                                   uint64_t &>
  static List<uint64_t> unfold(F0 &&f, uint64_t n, uint64_t seed) {
    return unfold_fuel(UINT64_C(100), f, n, seed);
  }

  /// tabulate n f generates f 0, f 1, ..., f (n-1) (same as init_list but
  /// different naming).
  static List<uint64_t> tabulate(uint64_t n, crane::fn<uint64_t(uint64_t)> f) {
    auto go_impl = [&](auto &, uint64_t i) -> List<uint64_t> {
      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        uint64_t i;
      };
      /// CraneCont_j: saves [f, i, n], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_j {
        crane::fn<uint64_t(uint64_t)> f;
        uint64_t i;
        uint64_t n;
      };
      using CraneFrame = std::variant<CraneEnter, CraneCont_j>;
      List<uint64_t> _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{i});
      /// Loopified go: CraneEnter -> CraneCont_j.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          uint64_t i = _f.i;
          if (i <= 0) {
            _result = List<uint64_t>::nil();
          } else {
            uint64_t j = i - 1;
            _stack.emplace_back(CraneCont_j{f, i, n});
            _stack.emplace_back(CraneEnter{j});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_j>(_frame));
          crane::fn<uint64_t(uint64_t)> f = std::move(_f.f);
          uint64_t i = _f.i;
          uint64_t n = _f.n;
          _result = List<uint64_t>::cons(f((((n - i) > n ? 0 : (n - i)))),
                                         std::move(_result));
        }
      }
      return _result;
    };
    auto go = [&](uint64_t i) -> List<uint64_t> { return go_impl(go_impl, i); };
    return go(n);
  }

  /// Helper: replicate single element n times.
  static List<uint64_t> replicate_single(uint64_t x, uint64_t n);
  /// replicate_each n l replicates each element n times: replicate_each 2 1,2
  /// -> 1,1,2,2.
  static List<uint64_t> replicate_each(uint64_t n, const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_GENERATORS
