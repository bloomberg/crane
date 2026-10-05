#ifndef INCLUDED_LOOPIFY_FOLDS
#define INCLUDED_LOOPIFY_FOLDS

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

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

struct LoopifyFolds {
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, const uint64_t &>
  static uint64_t fold_left(F0 &&f, uint64_t acc, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    uint64_t _loop_acc = acc;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return _loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        _loop_l = crane_raw(a1);
        _loop_acc = f(_loop_acc, a0);
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &&>
  static uint64_t
  fold_right(F0 &&f, const List<uint64_t> &l,
             uint64_t acc) { /// CraneEnter: captures varying parameters for
                             /// each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified fold_right: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = acc;
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        _result = f(a0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, const uint64_t &>
  static List<uint64_t> scanl(F0 &&f, uint64_t acc, const List<uint64_t> &l) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    const List<uint64_t> *_loop_l = &l;
    uint64_t _loop_acc = acc;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<uint64_t>::cons(_loop_acc, List<uint64_t>::nil());
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto _cell = typename List<uint64_t>::Cons(_loop_acc, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        _loop_acc = f(_loop_acc, a0);
        continue;
      }
    }
    return std::move(*_root);
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &&>
  static List<uint64_t>
  scanr(F0 &&f, uint64_t acc,
        const List<uint64_t> &l) { /// CraneEnter: captures varying parameters
                                   /// for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    List<uint64_t> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified scanr: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::cons(acc, List<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        List<uint64_t> _tmp1 = std::move(_result);
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _tmp1.v_mut())) {
          _result = List<uint64_t>::cons(acc, List<uint64_t>::nil());
        } else {
          auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_tmp1.v_mut());
          _result = List<uint64_t>::cons(f(a0, std::move(a00)), *a10);
        }
      }
    }
    return _result;
  }

  template <typename F1>
  static uint64_t foldl1_fuel(uint64_t fuel, F1 &&f, const List<uint64_t> &l) {
    List<uint64_t> _loop_l = l;
    uint64_t _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        return UINT64_C(0);
      } else {
        uint64_t fuel_ = _loop_fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
          return UINT64_C(0);
        } else {
          const auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(_loop_l.v());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
            return a0;
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(_sv0.v());
            _loop_l = List<uint64_t>::cons(f(a0, a00), *a10);
            _loop_fuel = fuel_;
          }
        }
      }
    }
  }

  template <typename F0>
  static uint64_t foldl1(F0 &&f, const List<uint64_t> &l) {
    return foldl1_fuel(l.length(), f, l);
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &&>
  static uint64_t
  foldr1(F0 &&f,
         const List<uint64_t> &l) { /// CraneEnter: captures varying parameters
                                    /// for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified foldr1: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = std::move(a0);
          } else {
            _stack.emplace_back(CraneCont_Cons{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        _result = f(a0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
  static std::pair<uint64_t, List<uint64_t>>
  map_accum(F0 &&f, uint64_t acc,
            const List<uint64_t> &l) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
      uint64_t acc;
    };

    /// CraneCont_acc_: saves [y], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_acc_ {
      uint64_t y;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_acc_>;
    std::pair<uint64_t, List<uint64_t>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l, acc});
    /// Loopified map_accum: CraneEnter -> CraneCont_acc_.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        uint64_t acc = _f.acc;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = std::make_pair(std::move(acc), List<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto [acc_, y] = f(acc, a0);
          _stack.emplace_back(CraneCont_acc_{y});
          _stack.emplace_back(CraneEnter{crane_raw(a1), acc_});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_acc_>(_frame));
        uint64_t y = _f.y;
        auto [final_acc, ys] = std::move(_result);
        _result =
            std::make_pair(final_acc, List<uint64_t>::cons(y, std::move(ys)));
      }
    }
    return _result;
  }

  template <typename F0>
  static List<uint64_t> iterate_accum(F0 &&f, uint64_t n, uint64_t x) {
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
        uint64_t n_ = _loop_n - 1;
        auto _cell = typename List<uint64_t>::Cons(_loop_x, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_x = f(_loop_x);
        _loop_n = n_;
        continue;
      }
    }
    return std::move(*_root);
  }

  template <typename F1>
  static List<uint64_t> unfold_fuel(uint64_t fuel, F1 &&f, uint64_t seed) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    uint64_t _loop_seed = seed;
    uint64_t _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t fuel_ = _loop_fuel - 1;
        auto [x, next_seed] = f(_loop_seed);
        auto _cell = typename List<uint64_t>::Cons(x, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_seed = next_seed;
        _loop_fuel = fuel_;
        continue;
      }
    }
    return std::move(*_root);
  }

  template <typename F1>
  static List<uint64_t> unfold(uint64_t x0_, F1 &&x1_, uint64_t x2_) {
    return unfold_fuel(x0_, x1_, x2_);
  }
};

#endif // INCLUDED_LOOPIFY_FOLDS
