#ifndef INCLUDED_LOOPIFY_HOFS
#define INCLUDED_LOOPIFY_HOFS

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

struct LoopifyHofs {
  /// foldl1 f l folds from left with no initial value. Returns 0 for empty
  /// list.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const T1 &>
  static T1 foldl1_aux(F0 &&f, T1 acc, const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    T1 _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return _loop_acc;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        _loop_l = crane_raw(a1);
        _loop_acc = f(std::move(_loop_acc), a0);
      }
    }
  }

  template <typename T1, typename F0>
  static T1 foldl1(F0 &&f, T1 default0, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return foldl1_aux<T1>(f, a0, *a1);
    }
  }

  /// forall_ p l checks if all elements satisfy predicate p.
  template <typename T1, typename F0>
  static bool forall_(F0 &&p, const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return true;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          _loop_l = crane_raw(a1);
        } else {
          return false;
        }
      }
    }
  }

  /// exists_fn p l checks if any element satisfies predicate p.
  template <typename T1, typename F0>
  static bool exists_fn(F0 &&p, const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return false;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          return true;
        } else {
          _loop_l = crane_raw(a1);
        }
      }
    }
  }

  /// drop_while p l drops elements while predicate holds.
  template <typename T1, typename F0>
  static List<T1> drop_while(F0 &&p, const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          _loop_l = crane_raw(a1);
        } else {
          return List<T1>::cons(a0, *a1);
        }
      }
    }
  }

  /// take_while p l takes elements while predicate holds.
  template <typename T1, typename F0>
  static List<T1> take_while(F0 &&p, const List<T1> &l) {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = typename List<T1>::Cons(a0, nullptr);
          List<T1> &_node =
              (_write
                   ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          auto _value = List<T1>::nil();
          (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        }
      }
    }
    return std::move(*_root);
  }

  /// flat_map f l maps f and flattens results.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<List<T2>, F0 &, T1 &>
  static List<T2>
  flat_map(F0 &&f, const List<T1> &l) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

    struct CraneEnter {
      const List<T1> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      T1 a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    List<T2> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified flat_map: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = List<T2>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        _result = f(a0).app(std::move(_result));
      }
    }
    return _result;
  }

  /// all_pairs l1 l2 returns all pairs from two lists.
  template <typename T1, typename T2>
  static List<std::pair<T1, T2>>
  all_pairs(const List<T1> &l1,
            const List<T2> &l2) { /// CraneEnter: captures varying parameters
                                  /// for each recursive call.

    struct CraneEnter {
      const List<T1> *l1;
    };

    /// CraneCont_Cons: saves [a00], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Cons {
      T1 a00;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    List<std::pair<T1, T2>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l1});
    /// Loopified all_pairs: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<T1> &l1 = *_f.l1;
        auto pair_with = [&](const T1 &x,
                             const List<T2> &l) -> List<std::pair<T1, T2>> {
          /// CraneEnter: captures varying parameters for each recursive call.
          struct CraneEnter {
            const List<T2> *l;
          };
          /// CraneCont_Cons: saves [a0], resumes after recursive call, then
          /// processes rest.
          struct CraneCont_Cons {
            T2 a0;
          };
          using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
          List<std::pair<T1, T2>> _result{};
          crane::small_vector<CraneFrame> _stack;
          _stack.emplace_back(CraneEnter{&l});
          /// Loopified pair_with: CraneEnter -> CraneCont_Cons.
          while (!_stack.empty()) {
            CraneFrame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<CraneEnter>(_frame)) {
              auto _f = std::move(std::get<CraneEnter>(_frame));
              const List<T2> &l = *_f.l;
              if (std::holds_alternative<typename List<T2>::Nil>(l.v())) {
                _result = List<std::pair<T1, T2>>::nil();
              } else {
                const auto &[a0, a1] = std::get<typename List<T2>::Cons>(l.v());
                _stack.emplace_back(CraneCont_Cons{a0});
                _stack.emplace_back(CraneEnter{crane_raw(a1)});
              }
            } else {
              auto _f = std::move(std::get<CraneCont_Cons>(_frame));
              auto a0 = std::move(_f.a0);
              _result = List<std::pair<T1, T2>>::cons(std::make_pair(x, a0),
                                                      std::move(_result));
            }
          }
          return _result;
        };
        if (std::holds_alternative<typename List<T1>::Nil>(l1.v())) {
          _result = List<std::pair<T1, T2>>::nil();
        } else {
          const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l1.v());
          _stack.emplace_back(CraneCont_Cons{a00});
          _stack.emplace_back(CraneEnter{crane_raw(a10)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a00 = std::move(_f.a00);
        auto pair_with = [&](const T1 &x,
                             const List<T2> &l) -> List<std::pair<T1, T2>> {
          /// CraneEnter: captures varying parameters for each recursive call.
          struct CraneEnter {
            const List<T2> *l;
          };
          /// CraneCont_Cons: saves [a0], resumes after recursive call, then
          /// processes rest.
          struct CraneCont_Cons {
            T2 a0;
          };
          using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
          List<std::pair<T1, T2>> _result{};
          crane::small_vector<CraneFrame> _stack;
          _stack.emplace_back(CraneEnter{&l});
          /// Loopified pair_with: CraneEnter -> CraneCont_Cons.
          while (!_stack.empty()) {
            CraneFrame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<CraneEnter>(_frame)) {
              auto _f = std::move(std::get<CraneEnter>(_frame));
              const List<T2> &l = *_f.l;
              if (std::holds_alternative<typename List<T2>::Nil>(l.v())) {
                _result = List<std::pair<T1, T2>>::nil();
              } else {
                const auto &[a0, a1] = std::get<typename List<T2>::Cons>(l.v());
                _stack.emplace_back(CraneCont_Cons{a0});
                _stack.emplace_back(CraneEnter{crane_raw(a1)});
              }
            } else {
              auto _f = std::move(std::get<CraneCont_Cons>(_frame));
              auto a0 = std::move(_f.a0);
              _result = List<std::pair<T1, T2>>::cons(std::make_pair(x, a0),
                                                      std::move(_result));
            }
          }
          return _result;
        };
        _result = pair_with(a00, l2).app(std::move(_result));
      }
    }
    return _result;
  }

  /// find_indices p l finds all indices where p is true.
  template <typename F0>
  static List<uint64_t> find_indices_aux(F0 &&p, const List<uint64_t> &l,
                                         uint64_t i) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    uint64_t _loop_i = std::move(i);
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = typename List<uint64_t>::Cons(_loop_i, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_i = (_loop_i + 1);
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_i = (_loop_i + 1);
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  template <typename F0>
  static List<uint64_t> find_indices(F0 &&p, const List<uint64_t> &l) {
    return find_indices_aux(p, l, UINT64_C(0));
  }

  /// delete_by eq x l deletes first element equal to x.
  template <typename F0>
  static List<uint64_t> delete_by(F0 &&eq, uint64_t x,
                                  const List<uint64_t> &l) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (eq(x, a0)) {
          auto _value = *a1;
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  static bool is_prefix_of(const List<uint64_t> &l1, const List<uint64_t> &l2);
  /// lookup_all key l finds all values associated with key in association list.
  static List<uint64_t>
  lookup_all(uint64_t key, const List<std::pair<uint64_t, uint64_t>> &l);

  /// scanl f acc l scan from left with accumulator.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, const uint64_t &>
  static List<uint64_t> scanl(F0 &&f, uint64_t acc, const List<uint64_t> &l) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    const List<uint64_t> *_loop_l = &l;
    uint64_t _loop_acc = std::move(acc);
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

  /// scanl1 f l like scanl but no initial value, uses first element.
  template <typename F1>
  static List<uint64_t> scanl1_fuel(uint64_t fuel, F1 &&f, List<uint64_t> l) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    List<uint64_t> _loop_l = std::move(l);
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        auto _value = std::move(_loop_l);
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t g = _loop_fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l.v_mut())) {
          auto _value = List<uint64_t>::nil();
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
            auto _value =
                List<uint64_t>::cons(std::move(a0), List<uint64_t>::nil());
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_value)))
                    : _root.emplace(std::move(_value)));
            break;
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(_sv0.v());
            auto _cell = typename List<uint64_t>::Cons(std::move(a0), nullptr);
            List<uint64_t> &_node =
                (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
            _loop_l = List<uint64_t>::cons(f(a0, a00), *a10);
            _loop_fuel = g;
            continue;
          }
        }
      }
    }
    return std::move(*_root);
  }

  template <typename F0>
  static List<uint64_t> scanl1(F0 &&f, const List<uint64_t> &l) {
    return scanl1_fuel(l.length(), f, l);
  }

  /// foldr1 f l fold right with no initial value.
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

  /// Helper: get head of list with default.
  static uint64_t head_default(uint64_t default0, const List<uint64_t> &l);

  /// scanr f acc l scan from right.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
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
        List<uint64_t> rest = std::move(_result);
        uint64_t h = head_default(acc, rest);
        _result = List<uint64_t>::cons(f(a0, h), std::move(rest));
      }
    }
    return _result;
  }

  /// scanr1 f l scanr with no initial value.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t>
  scanr1(F0 &&f,
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
    /// Loopified scanr1: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = List<uint64_t>::cons(a0, List<uint64_t>::nil());
          } else {
            _stack.emplace_back(CraneCont_Cons{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        List<uint64_t> rest = std::move(_result);
        uint64_t h = head_default(a0, rest);
        _result = List<uint64_t>::cons(f(a0, h), std::move(rest));
      }
    }
    return _result;
  }

  /// mapcat f l maps f and concatenates results (concat_map).
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<List<T1>, F0 &, uint64_t &>
  static List<T1>
  mapcat(F0 &&f,
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
    List<T1> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified mapcat: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        _result = f(a0).app(std::move(_result));
      }
    }
    return _result;
  }

  /// map_maybe f l maps f and filters out None results.
  template <typename F0>
    requires std::is_invocable_r_v<std::optional<uint64_t>, F0 &, uint64_t &>
  static List<uint64_t>
  map_maybe(F0 &&f,
            const List<uint64_t> &l) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

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
    /// Loopified map_maybe: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        List<uint64_t> rest = std::move(_result);
        auto _cs = f(a0);
        if (_cs.has_value()) {
          const uint64_t &y = *_cs;
          _result = List<uint64_t>::cons(y, std::move(rest));
        } else {
          _result = std::move(rest);
        }
      }
    }
    return _result;
  }

  /// bool_all p l checks if all elements satisfy p (same as forall_).
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool
  bool_all(F0 &&p,
           const List<uint64_t> &l) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    bool _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified bool_all: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = true;
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        _result = (p(a0) && std::move(_result));
      }
    }
    return _result;
  }

  /// merge_by cmp l1 l2 merges two lists using comparison function.
  template <typename F1>
  static List<uint64_t> merge_by_fuel(uint64_t fuel, F1 &&cmp,
                                      List<uint64_t> l1, List<uint64_t> l2) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    List<uint64_t> _loop_l2 = std::move(l2);
    List<uint64_t> _loop_l1 = std::move(l1);
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        auto _value = std::move(_loop_l1);
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t f = _loop_fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l1.v_mut())) {
          auto _value = std::move(_loop_l2);
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(_loop_l1.v_mut());
          if (std::holds_alternative<typename List<uint64_t>::Nil>(
                  _loop_l2.v_mut())) {
            auto _value = _loop_l1;
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_value)))
                    : _root.emplace(std::move(_value)));
            break;
          } else {
            auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(_loop_l2.v_mut());
            if (cmp(a0, a00) <= UINT64_C(0)) {
              auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
              List<uint64_t> &_node =
                  (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                  std::move(_cell)))
                          : _root.emplace(std::move(_cell)));
              _write =
                  &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
              _loop_l1 = List<uint64_t>(*a1);
              _loop_fuel = f;
              continue;
            } else {
              auto _cell = typename List<uint64_t>::Cons(a00, nullptr);
              List<uint64_t> &_node =
                  (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                  std::move(_cell)))
                          : _root.emplace(std::move(_cell)));
              _write =
                  &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
              _loop_l2 = List<uint64_t>(*a10);
              _loop_fuel = f;
              continue;
            }
          }
        }
      }
    }
    return std::move(*_root);
  }

  template <typename F0>
  static List<uint64_t> merge_by(F0 &&cmp, const List<uint64_t> &l1,
                                 const List<uint64_t> &l2) {
    return merge_by_fuel((l1.length() + l2.length()), cmp, l1, l2);
  }

  /// max_by f l finds element with maximum f value.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t
  max_by(F0 &&f,
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
    /// Loopified max_by: CraneEnter -> CraneCont_Cons.
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
            _result = f(a0);
          } else {
            _stack.emplace_back(CraneCont_Cons{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        uint64_t rest_max = std::move(_result);
        uint64_t fx = f(a0);
        if (rest_max <= fx) {
          _result = std::move(fx);
        } else {
          _result = std::move(rest_max);
        }
      }
    }
    return _result;
  }

  /// iterate f n x generates x, f(x), f(f(x)), ... of length n.
  template <typename F0>
  static List<uint64_t> iterate(F0 &&f, uint64_t n, uint64_t x) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    uint64_t _loop_x = std::move(x);
    uint64_t _loop_n = std::move(n);
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

  /// maximum_by cmp l finds maximum element by comparison function.
  template <typename F0>
  static uint64_t
  maximum_by(F0 &&cmp,
             const List<uint64_t> &l) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

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
    /// Loopified maximum_by: CraneEnter -> CraneCont_Cons.
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
        uint64_t m = std::move(_result);
        if (UINT64_C(0) <= cmp(a0, m)) {
          _result = std::move(a0);
        } else {
          _result = std::move(m);
        }
      }
    }
    return _result;
  }

  /// fold_right f l acc folds from the right.
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

  /// partition p l partitions list into (satisfies p, doesn't satisfy p).
  template <typename F0>
  static std::pair<List<uint64_t>, List<uint64_t>>
  partition(F0 &&p,
            const List<uint64_t> &l) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    std::pair<List<uint64_t>, List<uint64_t>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified partition: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result =
              std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        auto [yes, no] = std::move(_result);
        if (p(a0)) {
          _result = std::make_pair(List<uint64_t>::cons(a0, std::move(yes)),
                                   std::move(no));
        } else {
          _result = std::make_pair(std::move(yes),
                                   List<uint64_t>::cons(a0, std::move(no)));
        }
      }
    }
    return _result;
  }

  /// subsequences l generates all subsequences of l: 1,2 -> [],[1],[2],[1,2].
  static List<List<uint64_t>> subsequences(const List<uint64_t> &l);
  /// Helper: pair element with all elements in list.
  static List<std::pair<uint64_t, uint64_t>>
  pair_with_all(uint64_t x, const List<uint64_t> &l);
  /// cartesian l1 l2 computes cartesian product of two lists.
  static List<std::pair<uint64_t, uint64_t>>
  cartesian(const List<uint64_t> &l1, const List<uint64_t> &l2);
  /// longest_run l finds the longest consecutive run of equal elements.
  /// Matches on recursive result to decide behavior.
  static List<uint64_t> longest_run_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> longest_run(const List<uint64_t> &l);

  /// any p l checks if any element satisfies predicate (same as exists_fn but
  /// different name).
  template <typename F0> static bool any(F0 &&p, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return false;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          return true;
        } else {
          _loop_l = crane_raw(a1);
        }
      }
    }
  }

  /// all p l checks if all elements satisfy predicate (same as forall_ but
  /// different name).
  template <typename F0> static bool all(F0 &&p, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return true;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          _loop_l = crane_raw(a1);
        } else {
          return false;
        }
      }
    }
  }

  /// filter_not p l filters elements that don't satisfy predicate.
  template <typename F0>
  static List<uint64_t> filter_not(F0 &&p, const List<uint64_t> &l) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          _loop_l = crane_raw(a1);
          continue;
        } else {
          auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  /// span_split p l splits at first element that doesn't satisfy p.
  template <typename F0>
  static std::pair<List<uint64_t>, List<uint64_t>>
  span_split(F0 &&p,
             const List<uint64_t> &l) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont1: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont1 {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont1>;
    std::pair<List<uint64_t>, List<uint64_t>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified span_split: CraneEnter -> CraneCont1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result =
              std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(CraneCont1{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            _result = std::make_pair(List<uint64_t>::nil(),
                                     List<uint64_t>::cons(a0, *a1));
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont1>(_frame));
        uint64_t a0 = _f.a0;
        auto [taken, rest] = std::move(_result);
        _result = std::make_pair(List<uint64_t>::cons(a0, std::move(taken)),
                                 std::move(rest));
      }
    }
    return _result;
  }

  /// group_by_eq eq l groups consecutive elements by equality function.
  template <typename F1>
  static List<List<uint64_t>> group_by_eq_fuel(
      uint64_t fuel, F1 &&eq,
      const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
      uint64_t fuel;
    };

    /// CraneCont1: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont1 {
      uint64_t a0;
    };

    /// CraneCont2: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont2 {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
    List<List<uint64_t>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l, fuel});
    /// Loopified group_by_eq_fuel: CraneEnter -> CraneCont1 -> CraneCont2.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        uint64_t fuel = _f.fuel;
        if (fuel <= 0) {
          _result = List<List<uint64_t>>::nil();
        } else {
          uint64_t f = fuel - 1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
            _result = List<List<uint64_t>>::nil();
          } else {
            const auto &[a0, a1] =
                std::get<typename List<uint64_t>::Cons>(l.v());
            auto &&_sv0 = *a1;
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    _sv0.v())) {
              _result = List<List<uint64_t>>::cons(
                  List<uint64_t>::cons(a0, List<uint64_t>::nil()),
                  List<List<uint64_t>>::nil());
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<uint64_t>::Cons>(_sv0.v());
              if (eq(a0, a00)) {
                _stack.emplace_back(CraneCont1{a0});
                _stack.emplace_back(CraneEnter{crane_raw(a1), f});
              } else {
                _stack.emplace_back(CraneCont2{a0});
                _stack.emplace_back(CraneEnter{crane_raw(a1), f});
              }
            }
          }
        }
      } else if (std::holds_alternative<CraneCont1>(_frame)) {
        auto _f = std::move(std::get<CraneCont1>(_frame));
        uint64_t a0 = _f.a0;
        List<List<uint64_t>> _tmp1 = std::move(_result);
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                _tmp1.v_mut())) {
          _result = List<List<uint64_t>>::cons(
              List<uint64_t>::cons(a0, List<uint64_t>::nil()),
              List<List<uint64_t>>::nil());
        } else {
          auto &[a01, a11] =
              std::get<typename List<List<uint64_t>>::Cons>(_tmp1.v_mut());
          _result = List<List<uint64_t>>::cons(
              List<uint64_t>::cons(a0, std::move(a01)), *a11);
        }
      } else {
        auto _f = std::move(std::get<CraneCont2>(_frame));
        uint64_t a0 = _f.a0;
        _result = List<List<uint64_t>>::cons(
            List<uint64_t>::cons(a0, List<uint64_t>::nil()),
            std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
  static List<List<uint64_t>> group_by_eq(F0 &&eq, const List<uint64_t> &l) {
    return group_by_eq_fuel(l.length(), eq, l);
  }

  /// power_set l generates all subsets.
  static List<List<uint64_t>> power_set(const List<uint64_t> &l);

  /// map_accum_l f acc l maps with accumulator threading.
  template <typename F0>
  static std::pair<uint64_t, List<uint64_t>>
  map_accum_l(F0 &&f, uint64_t acc,
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
    /// Loopified map_accum_l: CraneEnter -> CraneCont_acc_.
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
        auto [acc_p, ys] = std::move(_result);
        _result = std::make_pair(acc_p, List<uint64_t>::cons(y, std::move(ys)));
      }
    }
    return _result;
  }
};

#endif // INCLUDED_LOOPIFY_HOFS
