#ifndef INCLUDED_LOOPIFY_TMC
#define INCLUDED_LOOPIFY_TMC

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

/// Tests for Tail Modulo Cons (TMC) loopification optimization.
/// Functions where the recursive call is wrapped in a single constructor
/// should be optimized to use O(1) extra space via destination-passing style.
struct LoopifyTmc {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<list<A>> l;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    list(const list<CraneU> &_other)
        : v_(crane_convert_spine(
              _other, std::shared_ptr<list<A>>(nullptr),
              [](const list<CraneU> &_cell) -> const list<CraneU> * {
                if (std::holds_alternative<typename list<CraneU>::Cons>(
                        _cell.v())) {
                  return std::get<typename list<CraneU>::Cons>(_cell.v())
                      .l.get();
                } else {
                  return nullptr;
                }
              },
              [&](const list<CraneU> &_other,
                  std::shared_ptr<list<A>> _below) -> variant_t {
                if (std::holds_alternative<typename list<CraneU>::Nil>(
                        _other.v())) {
                  return Nil{};
                } else {
                  const auto &[a, l] =
                      std::get<typename list<CraneU>::Cons>(_other.v());
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
                return std::make_shared<list<A>>(std::move(_alt));
              })) {}

    static list<A> nil() { return list<A>(Nil{}); }

    static list<A> cons(A a, list<A> l) {
      return list<A>(
          Cons{std::move(a), std::make_shared<list<A>>(std::move(l))});
    }

    // MANIPULATORS
    ~list() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<list<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->l);
          }
        }
        return nullptr;
      };
      std::shared_ptr<list<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2
  list_rect(T2 f, F1 &&f0,
            const list<T1> &l) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

    struct CraneEnter {
      const list<T1> *l;
    };

    /// CraneCont_Cons: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Cons {
      T1 a0;
      std::shared_ptr<list<T1>> a1;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    T2 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified list_rect: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0, a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        std::shared_ptr<list<T1>> a1 = std::move(_f.a1);
        _result = f0(a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
  static T2 list_rec(const T2 &f, F1 &&f0, const list<T1> &l) {
    return list_rect<T1, T2>(f, f0, l);
  }

  /// app l1 l2 appends two lists. Basic TMC pattern: cons head (app tail l2).
  template <typename T1> static list<T1> app(const list<T1> &l1, list<T1> l2) {
    std::optional<list<T1>> _root{};
    std::shared_ptr<list<T1>> *_write = nullptr;
    list<T1> _loop_l2 = std::move(l2);
    const list<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1->v())) {
        auto _value = std::move(_loop_l2);
        (_write ? *(*_write = std::make_shared<list<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l1->v());
        auto _cell = typename list<T1>::Cons(a0, nullptr);
        list<T1> &_node =
            (_write ? *(*_write = std::make_shared<list<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename list<T1>::Cons>(_node.v_mut()).l;
        _loop_l1 = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }

  /// map f l applies f to every element. TMC with element transform.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const T1 &>
  static list<T2> map(F0 &&f, const list<T1> &l) {
    std::optional<list<T2>> _root{};
    std::shared_ptr<list<T2>> *_write = nullptr;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        auto _value = list<T2>::nil();
        (_write ? *(*_write = std::make_shared<list<T2>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cell = typename list<T2>::Cons(f(a0), nullptr);
        list<T2> &_node =
            (_write ? *(*_write = std::make_shared<list<T2>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename list<T2>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }

  /// filter f l keeps elements satisfying f. Mixed tail + TMC branches.
  template <typename T1, typename F0>
  static list<T1> filter(F0 &&f, const list<T1> &l) {
    std::optional<list<T1>> _root{};
    std::shared_ptr<list<T1>> *_write = nullptr;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        auto _value = list<T1>::nil();
        (_write ? *(*_write = std::make_shared<list<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        if (f(a0)) {
          auto _cell = typename list<T1>::Cons(a0, nullptr);
          list<T1> &_node =
              (_write
                   ? *(*_write = std::make_shared<list<T1>>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
          _write = &std::get<typename list<T1>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  /// snoc l x appends x at the end. TMC, base case allocates a cell.
  template <typename T1> static list<T1> snoc(const list<T1> &l, const T1 &x) {
    std::optional<list<T1>> _root{};
    std::shared_ptr<list<T1>> *_write = nullptr;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        auto _value = list<T1>::cons(x, list<T1>::nil());
        (_write ? *(*_write = std::make_shared<list<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cell = typename list<T1>::Cons(a0, nullptr);
        list<T1> &_node =
            (_write ? *(*_write = std::make_shared<list<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename list<T1>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }

  /// replicate n x creates n copies of x. Nat recursion producing list.
  template <typename T1> static list<T1> replicate(uint64_t n, const T1 &x) {
    std::optional<list<T1>> _root{};
    std::shared_ptr<list<T1>> *_write = nullptr;
    uint64_t _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        auto _value = list<T1>::nil();
        (_write ? *(*_write = std::make_shared<list<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t m = _loop_n - 1;
        auto _cell = typename list<T1>::Cons(x, nullptr);
        list<T1> &_node =
            (_write ? *(*_write = std::make_shared<list<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename list<T1>::Cons>(_node.v_mut()).l;
        _loop_n = m;
        continue;
      }
    }
    return std::move(*_root);
  }

  /// range lo hi creates lo, lo+1, ..., hi-1.
  static list<uint64_t> range(uint64_t lo, uint64_t hi);

  /// zip_with f l1 l2 combines two lists element-wise. Two varying params.
  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, const T1 &, const T2 &>
  static list<T3> zip_with(F0 &&f, const list<T1> &l1, const list<T2> &l2) {
    std::optional<list<T3>> _root{};
    std::shared_ptr<list<T3>> *_write = nullptr;
    const list<T2> *_loop_l2 = &l2;
    const list<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1->v())) {
        auto _value = list<T3>::nil();
        (_write ? *(*_write = std::make_shared<list<T3>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2->v())) {
          auto _value = list<T3>::nil();
          (_write ? *(*_write = std::make_shared<list<T3>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename list<T2>::Cons>(_loop_l2->v());
          auto _cell = typename list<T3>::Cons(f(a0, a00), nullptr);
          list<T3> &_node =
              (_write
                   ? *(*_write = std::make_shared<list<T3>>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
          _write = &std::get<typename list<T3>::Cons>(_node.v_mut()).l;
          _loop_l2 = crane_raw(a10);
          _loop_l1 = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  /// prefix_sums acc l computes running prefix sums.
  static list<uint64_t> prefix_sums(uint64_t acc, const list<uint64_t> &l);

  /// stutter l duplicates each element: 1,2 -> 1,1,2,2. Nested TMC.
  template <typename T1> static list<T1> stutter(const list<T1> &l) {
    std::optional<list<T1>> _root{};
    std::shared_ptr<list<T1>> *_write = nullptr;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        auto _value = list<T1>::nil();
        (_write ? *(*_write = std::make_shared<list<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cell1 =
            std::make_shared<list<T1>>(typename list<T1>::Cons(a0, nullptr));
        auto _cell = typename list<T1>::Cons(a0, std::move(_cell1));
        list<T1> &_node =
            (_write ? *(*_write = std::make_shared<list<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename list<T1>::Cons>(
                 std::get<typename list<T1>::Cons>(_node.v_mut()).l->v_mut())
                 .l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

#endif // INCLUDED_LOOPIFY_TMC
