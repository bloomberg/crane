#ifndef INCLUDED_LOOPIFY_GENERATORS
#define INCLUDED_LOOPIFY_GENERATORS

#include "crane_fn.h"
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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
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

/// Consolidated list generator functions.
struct LoopifyGenerators {
  /// cycle n l repeats the list n times: cycle 2 1,2 -> 1,2,1,2.
  static List<uint64_t> cycle(uint64_t n, const List<uint64_t> &l);

  /// iterate f n x applies f repeatedly n times: iterate (+1) 3 5 -> 5,6,7.
  template <typename F0>
  static List<uint64_t> iterate(F0 &&f, uint64_t n, uint64_t x) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    uint64_t _loop_x = x;
    uint64_t _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t m = _loop_n - 1;
        auto _cell = typename List<uint64_t>::Cons(_loop_x, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_x = f(_loop_x);
        _loop_n = m;
        continue;
      }
    }
    return std::move(*_root);
  }

  /// zip_with f l1 l2 zips with a combining function.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &,
                                   const uint64_t &>
  static List<uint64_t> zip_with(F0 &&f, const List<uint64_t> &l1,
                                 const List<uint64_t> &l2) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    const List<uint64_t> *_loop_l2 = &l2;
    const List<uint64_t> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l2->v())) {
          auto _value = List<uint64_t>::nil();
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
          auto _cell = typename List<uint64_t>::Cons(f(a0, a00), nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l2 = crane_raw(a10);
          _loop_l1 = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
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
  static List<uint64_t> unfold_fuel(uint64_t fuel, F1 &&f, uint64_t n,
                                    uint64_t seed) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    uint64_t _loop_seed = seed;
    uint64_t _loop_n = n;
    uint64_t _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t g = _loop_fuel - 1;
        if (_loop_n == UINT64_C(0)) {
          auto _value = List<uint64_t>::nil();
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          auto [val, next_seed] = f(_loop_seed);
          auto _cell = typename List<uint64_t>::Cons(val, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_seed = next_seed;
          _loop_n = ((
              (_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
          _loop_fuel = g;
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  template <typename F0>
  static List<uint64_t> unfold(F0 &&f, uint64_t n, uint64_t seed) {
    return unfold_fuel(UINT64_C(100), f, n, seed);
  }

  /// tabulate n f generates f 0, f 1, ..., f (n-1) (same as init_list but
  /// different naming).
  template <typename F1> static List<uint64_t> tabulate(uint64_t n, F1 &&f) {
    {
      uint64_t _lc1_i = n;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        uint64_t i;
      };

      /// CraneCont_j: saves [f, i, n], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_j {
        std::decay_t<F1> f;
        uint64_t i;
        uint64_t n;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_j>;
      List<uint64_t> _lc1_result{};
      crane::small_vector<CraneFrame> _lc1_stack;
      _lc1_stack.emplace_back(CraneEnter{_lc1_i});
      /// Loopified go: CraneEnter -> CraneCont_j.
      while (!_lc1_stack.empty()) {
        CraneFrame _frame = std::move(_lc1_stack.back());
        _lc1_stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          uint64_t _lc1_i = _f.i;
          if (_lc1_i <= 0) {
            _lc1_result = List<uint64_t>::nil();
          } else {
            uint64_t j = _lc1_i - 1;
            _lc1_stack.emplace_back(CraneCont_j{std::move(f), _lc1_i, n});
            _lc1_stack.emplace_back(CraneEnter{j});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_j>(_frame));
          std::decay_t<F1> f = std::move(_f.f);
          uint64_t _lc1_i = _f.i;
          uint64_t n = _f.n;
          _lc1_result =
              List<uint64_t>::cons(f((((n - _lc1_i) > n ? 0 : (n - _lc1_i)))),
                                   std::move(_lc1_result));
        }
      }
      return _lc1_result;
    }
  }

  /// Helper: replicate single element n times.
  static List<uint64_t> replicate_single(uint64_t x, uint64_t n);
  /// replicate_each n l replicates each element n times: replicate_each 2 1,2
  /// -> 1,1,2,2.
  static List<uint64_t> replicate_each(uint64_t n, const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_GENERATORS
