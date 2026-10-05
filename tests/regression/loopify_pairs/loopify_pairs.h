#ifndef INCLUDED_LOOPIFY_PAIRS
#define INCLUDED_LOOPIFY_PAIRS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

/// Consolidated UNIQUE pair/tuple operations.
struct LoopifyPairs {
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
        : v_([&]() -> variant_t {
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
                  (l ? std::make_shared<list<A>>(crane_convert<list<A>>(*l))
                     : nullptr)};
            }
          }()) {}

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

  /// partition p l splits into (satisfies p, doesn't satisfy p).
  template <typename T1, typename F0>
  static std::pair<list<T1>, list<T1>>
  partition(F0 &&p, const list<T1> &l) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

    struct CraneEnter {
      const list<T1> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      T1 a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    std::pair<list<T1>, list<T1>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified partition: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        auto [yes, no] = std::move(_result);
        if (p(a0)) {
          _result =
              std::make_pair(list<T1>::cons(a0, std::move(yes)), std::move(no));
        } else {
          _result =
              std::make_pair(std::move(yes), list<T1>::cons(a0, std::move(no)));
        }
      }
    }
    return _result;
  }

  /// unzip l splits list of nat pairs into pair of lists.
  static std::pair<list<uint64_t>, list<uint64_t>>
  unzip(const list<std::pair<uint64_t, uint64_t>> &l);

  /// zip combines two lists into pairs.
  template <typename T1, typename T2>
  static list<std::pair<T1, T2>> zip(const list<T1> &l1, const list<T2> &l2) {
    std::optional<list<std::pair<T1, T2>>> _root{};
    std::shared_ptr<list<std::pair<T1, T2>>> *_write = nullptr;
    const list<T2> *_loop_l2 = &l2;
    const list<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1->v())) {
        auto _value = list<std::pair<T1, T2>>::nil();
        (_write ? *(*_write = std::make_shared<list<std::pair<T1, T2>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2->v())) {
          auto _value = list<std::pair<T1, T2>>::nil();
          (_write ? *(*_write = std::make_shared<list<std::pair<T1, T2>>>(
                          std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename list<T2>::Cons>(_loop_l2->v());
          auto _cell = typename list<std::pair<T1, T2>>::Cons(
              std::make_pair(a0, a00), nullptr);
          list<std::pair<T1, T2>> &_node =
              (_write ? *(*_write = std::make_shared<list<std::pair<T1, T2>>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename list<std::pair<T1, T2>>::Cons>(_node.v_mut())
                   .l;
          _loop_l2 = crane_raw(a10);
          _loop_l1 = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  /// zip3 combines three lists.
  template <typename T1, typename T2, typename T3>
  static list<std::pair<T1, std::pair<T2, T3>>>
  zip3(const list<T1> &l1, const list<T2> &l2, const list<T3> &l3) {
    std::optional<list<std::pair<T1, std::pair<T2, T3>>>> _root{};
    std::shared_ptr<list<std::pair<T1, std::pair<T2, T3>>>> *_write = nullptr;
    const list<T3> *_loop_l3 = &l3;
    const list<T2> *_loop_l2 = &l2;
    const list<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1->v())) {
        auto _value = list<std::pair<T1, std::pair<T2, T3>>>::nil();
        (_write
             ? *(*_write =
                     std::make_shared<list<std::pair<T1, std::pair<T2, T3>>>>(
                         std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2->v())) {
          auto _value = list<std::pair<T1, std::pair<T2, T3>>>::nil();
          (_write
               ? *(*_write =
                       std::make_shared<list<std::pair<T1, std::pair<T2, T3>>>>(
                           std::move(_value)))
               : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename list<T2>::Cons>(_loop_l2->v());
          if (std::holds_alternative<typename list<T3>::Nil>(_loop_l3->v())) {
            auto _value = list<std::pair<T1, std::pair<T2, T3>>>::nil();
            (_write ? *(*_write = std::make_shared<
                            list<std::pair<T1, std::pair<T2, T3>>>>(
                            std::move(_value)))
                    : _root.emplace(std::move(_value)));
            break;
          } else {
            const auto &[a01, a11] =
                std::get<typename list<T3>::Cons>(_loop_l3->v());
            auto _cell = typename list<std::pair<T1, std::pair<T2, T3>>>::Cons(
                std::make_pair(a0, std::make_pair(a00, a01)), nullptr);
            list<std::pair<T1, std::pair<T2, T3>>> &_node =
                (_write ? *(*_write = std::make_shared<
                                list<std::pair<T1, std::pair<T2, T3>>>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write =
                &std::get<
                     typename list<std::pair<T1, std::pair<T2, T3>>>::Cons>(
                     _node.v_mut())
                     .l;
            _loop_l3 = crane_raw(a11);
            _loop_l2 = crane_raw(a10);
            _loop_l1 = crane_raw(a1);
            continue;
          }
        }
      }
    }
    return std::move(*_root);
  }

  /// split_at n l splits at position n.
  template <typename T1>
  static std::pair<list<T1>, list<T1>>
  split_at(uint64_t n,
           const list<T1> &l) { /// CraneEnter: captures varying parameters for
                                /// each recursive call.

    struct CraneEnter {
      const list<T1> *l;
      uint64_t n;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      T1 a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    std::pair<list<T1>, list<T1>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l, n});
    /// Loopified split_at: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<T1> &l = *_f.l;
        uint64_t n = _f.n;
        if (n <= 0) {
          _result = std::make_pair(list<T1>::nil(), l);
        } else {
          uint64_t m = n - 1;
          if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
            _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
          } else {
            const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
            _stack.emplace_back(CraneCont_Cons{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1), m});
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        auto [taken, rest] = std::move(_result);
        _result = std::make_pair(list<T1>::cons(a0, std::move(taken)),
                                 std::move(rest));
      }
    }
    return _result;
  }

  /// swizzle separates into even/odd positions.
  template <typename T1>
  static std::pair<list<T1>, list<T1>>
  swizzle(const list<T1> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

    struct CraneEnter {
      const list<T1> *l;
    };

    /// CraneCont_Cons: saves [a0, a00], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Cons {
      T1 a0;
      T1 a00;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    std::pair<list<T1>, list<T1>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified swizzle: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename list<T1>::Nil>(_sv0.v())) {
            _result = std::make_pair(list<T1>::cons(a0, list<T1>::nil()),
                                     list<T1>::nil());
          } else {
            const auto &[a00, a10] =
                std::get<typename list<T1>::Cons>(_sv0.v());
            _stack.emplace_back(CraneCont_Cons{a0, a00});
            _stack.emplace_back(CraneEnter{crane_raw(a10)});
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        auto a00 = std::move(_f.a00);
        auto [evens, odds] = std::move(_result);
        _result = std::make_pair(list<T1>::cons(a0, std::move(evens)),
                                 list<T1>::cons(a00, std::move(odds)));
      }
    }
    return _result;
  }

  /// span p l splits at first element not satisfying p.
  template <typename T1, typename F0>
  static std::pair<list<T1>, list<T1>>
  span(F0 &&p, const list<T1> &l) { /// CraneEnter: captures varying parameters
                                    /// for each recursive call.

    struct CraneEnter {
      const list<T1> *l;
    };

    /// CraneCont1: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont1 {
      T1 a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont1>;
    std::pair<list<T1>, list<T1>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified span: CraneEnter -> CraneCont1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(CraneCont1{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            _result = std::make_pair(list<T1>::nil(), list<T1>::cons(a0, *a1));
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont1>(_frame));
        auto a0 = std::move(_f.a0);
        auto [ys, zs] = std::move(_result);
        _result =
            std::make_pair(list<T1>::cons(a0, std::move(ys)), std::move(zs));
      }
    }
    return _result;
  }

  /// partition3 pivot l three-way partition around pivot.
  static std::pair<list<uint64_t>, std::pair<list<uint64_t>, list<uint64_t>>>
  partition3(uint64_t pivot, const list<uint64_t> &l);
  /// min_max l finds both min and max in one pass.
  static std::pair<uint64_t, uint64_t> min_max(const list<uint64_t> &l);
  /// sum_and_count computes both in one pass.
  static std::pair<uint64_t, uint64_t> sum_and_count(const list<uint64_t> &l);
  /// sum_prod_count triple accumulator.
  static std::pair<uint64_t, std::pair<uint64_t, uint64_t>>
  sum_prod_count(const list<uint64_t> &l);

  /// mapAccumL f acc l map with accumulator threading.
  template <typename F0>
  static std::pair<uint64_t, list<uint64_t>>
  mapAccumL(F0 &&f, uint64_t acc,
            const list<uint64_t> &l) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

    struct CraneEnter {
      const list<uint64_t> *l;
      uint64_t acc;
    };

    /// CraneCont_acc_: saves [y], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_acc_ {
      uint64_t y;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_acc_>;
    std::pair<uint64_t, list<uint64_t>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l, acc});
    /// Loopified mapAccumL: CraneEnter -> CraneCont_acc_.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<uint64_t> &l = *_f.l;
        uint64_t acc = _f.acc;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = std::make_pair(std::move(acc), list<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          auto [acc_, y] = f(acc, a0);
          _stack.emplace_back(CraneCont_acc_{y});
          _stack.emplace_back(CraneEnter{crane_raw(a1), acc_});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_acc_>(_frame));
        uint64_t y = _f.y;
        auto [final_acc, ys] = std::move(_result);
        _result =
            std::make_pair(final_acc, list<uint64_t>::cons(y, std::move(ys)));
      }
    }
    return _result;
  }

  /// lookup_all key l finds all values associated with key.
  static list<uint64_t>
  lookup_all(uint64_t key, const list<std::pair<uint64_t, uint64_t>> &l);
  /// swap_pairs l swaps elements in each pair.
  static list<std::pair<uint64_t, uint64_t>>
  swap_pairs(const list<std::pair<uint64_t, uint64_t>> &l);
};

#endif // INCLUDED_LOOPIFY_PAIRS
