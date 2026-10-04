#ifndef INCLUDED_LOOPIFY_LISTS
#define INCLUDED_LOOPIFY_LISTS

#include "crane_fn.h"
#include "fn.h"
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

/// Consolidated UNIQUE list operations - no stdlib duplicates.
/// Tests loopification on domain-specific list algorithms.
struct LoopifyLists {
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
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
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
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2
  list_rec(T2 f, F1 &&f0,
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
    /// Loopified list_rec: CraneEnter -> CraneCont_Cons.
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

  /// stutter l duplicates each element: 1,2 -> 1,1,2,2.
  template <typename T1> static list<T1> stutter(const list<T1> &l) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<list<T1>>(list<T1>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cell =
            std::make_shared<list<T1>>(typename list<T1>::Cons(a0, nullptr));
        auto _cell1 =
            std::make_shared<list<T1>>(typename list<T1>::Cons(a0, nullptr));
        std::get<typename list<T1>::Cons>(_cell->v_mut()).l = std::move(_cell1);
        *_write = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>(
                      std::get<typename list<T1>::Cons>((*_write)->v_mut())
                          .l->v_mut())
                      .l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }

  /// snoc l x appends x at the end (reverse cons).
  template <typename T1> static list<T1> snoc(const list<T1> &l, const T1 &x) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write =
            std::make_shared<list<T1>>(list<T1>::cons(x, list<T1>::nil()));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cell =
            std::make_shared<list<T1>>(typename list<T1>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>((*_write)->v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }

  /// intersperse sep l inserts separator between elements.
  template <typename T1>
  static list<T1> intersperse(const T1 &sep, const list<T1> &l) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<list<T1>>(list<T1>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename list<T1>::Nil>(_sv.v())) {
          *_write =
              std::make_shared<list<T1>>(list<T1>::cons(a0, list<T1>::nil()));
          break;
        } else {
          auto _cell =
              std::make_shared<list<T1>>(typename list<T1>::Cons(a0, nullptr));
          auto _cell1 =
              std::make_shared<list<T1>>(typename list<T1>::Cons(sep, nullptr));
          std::get<typename list<T1>::Cons>(_cell->v_mut()).l =
              std::move(_cell1);
          *_write = std::move(_cell);
          _write = &std::get<typename list<T1>::Cons>(
                        std::get<typename list<T1>::Cons>((*_write)->v_mut())
                            .l->v_mut())
                        .l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// replicate n x creates n copies of x.
  template <typename T1> static list<T1> replicate(uint64_t n, const T1 &x) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> *_write = &_head;
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        *_write = std::make_shared<list<T1>>(list<T1>::nil());
        break;
      } else {
        uint64_t m = _loop_n - 1;
        auto _cell =
            std::make_shared<list<T1>>(typename list<T1>::Cons(x, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>((*_write)->v_mut()).l;
        _loop_n = m;
        continue;
      }
    }
    return std::move(*_head);
  }

  /// replicate_list n l repeats list l n times.
  template <typename T1>
  static list<T1>
  replicate_list(uint64_t n,
                 const list<T1> &l) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

    struct CraneEnter {
      uint64_t n;
    };

    /// CraneCont_m: resumes after recursive call, then processes rest.
    struct CraneCont_m {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
    list<T1> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{n});
    /// Loopified replicate_list: CraneEnter -> CraneCont_m.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        uint64_t n = _f.n;
        auto app_impl = [&](auto &, const list<T1> &l1,
                            list<T1> l2) -> list<T1> {
          /// CraneEnter: captures varying parameters for each recursive call.
          struct CraneEnter {
            list<T1> l2;
            const list<T1> *l1;
          };
          /// CraneCont_Cons: saves [a0], resumes after recursive call, then
          /// processes rest.
          struct CraneCont_Cons {
            T1 a0;
          };
          using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
          list<T1> _result{};
          crane::small_vector<CraneFrame> _stack;
          _stack.emplace_back(CraneEnter{std::move(l2), &l1});
          /// Loopified app: CraneEnter -> CraneCont_Cons.
          while (!_stack.empty()) {
            CraneFrame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<CraneEnter>(_frame)) {
              auto _f = std::move(std::get<CraneEnter>(_frame));
              list<T1> l2 = std::move(_f.l2);
              const list<T1> &l1 = *_f.l1;
              if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
                _result = std::move(l2);
              } else {
                const auto &[a0, a1] =
                    std::get<typename list<T1>::Cons>(l1.v());
                _stack.emplace_back(CraneCont_Cons{a0});
                _stack.emplace_back(CraneEnter{std::move(l2), crane_raw(a1)});
              }
            } else {
              auto _f = std::move(std::get<CraneCont_Cons>(_frame));
              auto a0 = std::move(_f.a0);
              _result = list<T1>::cons(a0, std::move(_result));
            }
          }
          return _result;
        };
        auto app = [&](const list<T1> &l1, list<T1> l2) -> list<T1> {
          return app_impl(app_impl, l1, l2);
        };
        if (n <= 0) {
          _result = list<T1>::nil();
        } else {
          uint64_t m = n - 1;
          _stack.emplace_back(CraneCont_m{});
          _stack.emplace_back(CraneEnter{m});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_m>(_frame));
        auto app_impl = [&](auto &, const list<T1> &l1,
                            list<T1> l2) -> list<T1> {
          /// CraneEnter: captures varying parameters for each recursive call.
          struct CraneEnter {
            list<T1> l2;
            const list<T1> *l1;
          };
          /// CraneCont_Cons: saves [a0], resumes after recursive call, then
          /// processes rest.
          struct CraneCont_Cons {
            T1 a0;
          };
          using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
          list<T1> _result{};
          crane::small_vector<CraneFrame> _stack;
          _stack.emplace_back(CraneEnter{std::move(l2), &l1});
          /// Loopified app: CraneEnter -> CraneCont_Cons.
          while (!_stack.empty()) {
            CraneFrame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<CraneEnter>(_frame)) {
              auto _f = std::move(std::get<CraneEnter>(_frame));
              list<T1> l2 = std::move(_f.l2);
              const list<T1> &l1 = *_f.l1;
              if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
                _result = std::move(l2);
              } else {
                const auto &[a0, a1] =
                    std::get<typename list<T1>::Cons>(l1.v());
                _stack.emplace_back(CraneCont_Cons{a0});
                _stack.emplace_back(CraneEnter{std::move(l2), crane_raw(a1)});
              }
            } else {
              auto _f = std::move(std::get<CraneCont_Cons>(_frame));
              auto a0 = std::move(_f.a0);
              _result = list<T1>::cons(a0, std::move(_result));
            }
          }
          return _result;
        };
        auto app = [&](const list<T1> &l1, list<T1> l2) -> list<T1> {
          return app_impl(app_impl, l1, l2);
        };
        _result = app(l, std::move(_result));
      }
    }
    return _result;
  }

  /// init_list n f generates f 0, f 1, ..., f (n-1).
  template <typename T1>
  static list<T1> init_list(uint64_t n,
                            std::type_identity_t<crane::fn<T1(uint64_t)>> f) {
    auto go_impl = [&](auto &, uint64_t i) -> list<T1> {
      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        uint64_t i;
      };
      /// CraneCont_j: saves [f, i, n], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_j {
        std::type_identity_t<crane::fn<T1(uint64_t)>> f;
        uint64_t i;
        uint64_t n;
      };
      using CraneFrame = std::variant<CraneEnter, CraneCont_j>;
      list<T1> _result{};
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
            _result = list<T1>::nil();
          } else {
            uint64_t j = i - 1;
            _stack.emplace_back(CraneCont_j{f, i, n});
            _stack.emplace_back(CraneEnter{j});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_j>(_frame));
          std::type_identity_t<crane::fn<T1(uint64_t)>> f = std::move(_f.f);
          uint64_t i = _f.i;
          uint64_t n = _f.n;
          _result = list<T1>::cons(f((((n - i) > n ? 0 : (n - i)))),
                                   std::move(_result));
        }
      }
      return _result;
    };
    auto go = [&](uint64_t i) -> list<T1> { return go_impl(go_impl, i); };
    return go(n);
  }

  /// range start count generates start, start+1, ..., start+count-1.
  static list<uint64_t> range(uint64_t start, uint64_t count0);

  /// tails l returns all suffixes.
  template <typename T1> static list<list<T1>> tails(const list<T1> &l) {
    std::shared_ptr<list<list<T1>>> _head{};
    std::shared_ptr<list<list<T1>>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<list<list<T1>>>(
            list<list<T1>>::cons(list<T1>::nil(), list<list<T1>>::nil()));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cell = std::make_shared<list<list<T1>>>(
            typename list<list<T1>>::Cons(*_loop_l, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<list<T1>>::Cons>((*_write)->v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }

  /// inits l returns all prefixes (complex recursion pattern).
  template <typename T1>
  static list<list<T1>>
  inits(const list<T1> &l) { /// CraneEnter: captures varying parameters for
                             /// each recursive call.

    struct CraneEnter {
      const list<T1> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      T1 a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    list<list<T1>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified inits: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result =
              list<list<T1>>::cons(list<T1>::nil(), list<list<T1>>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        list<list<T1>> _tmp2 = std::move(_result);
        _result = list<list<T1>>::cons(list<T1>::nil(), [&]() {
          auto map_cons_impl = [&](auto &,
                                   const list<list<T1>> &ys) -> list<list<T1>> {
            /// CraneEnter: captures varying parameters for each recursive call.
            struct CraneEnter {
              const list<list<T1>> *ys;
            };
            /// CraneCont_Cons: saves [a0, a2], resumes after recursive call,
            /// then processes rest.
            struct CraneCont_Cons {
              std::decay_t<decltype(a0)> a0;
              list<T1> a2;
            };
            using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
            list<list<T1>> _result{};
            crane::small_vector<CraneFrame> _stack;
            _stack.emplace_back(CraneEnter{&ys});
            /// Loopified map_cons: CraneEnter -> CraneCont_Cons.
            while (!_stack.empty()) {
              CraneFrame _frame = std::move(_stack.back());
              _stack.pop_back();
              if (std::holds_alternative<CraneEnter>(_frame)) {
                auto _f = std::move(std::get<CraneEnter>(_frame));
                const list<list<T1>> &ys = *_f.ys;
                if (std::holds_alternative<typename list<list<T1>>::Nil>(
                        ys.v())) {
                  _result = list<list<T1>>::nil();
                } else {
                  const auto &[a2, a3] =
                      std::get<typename list<list<T1>>::Cons>(ys.v());
                  _stack.emplace_back(CraneCont_Cons{a0, a2});
                  _stack.emplace_back(CraneEnter{crane_raw(a3)});
                }
              } else {
                auto _f = std::move(std::get<CraneCont_Cons>(_frame));
                a0 = _f.a0;
                list<T1> a2 = std::move(_f.a2);
                _result = list<list<T1>>::cons(list<T1>::cons(a0, a2),
                                               std::move(_result));
              }
            }
            return _result;
          };
          auto map_cons = [&](const list<list<T1>> &ys) -> list<list<T1>> {
            return map_cons_impl(map_cons_impl, ys);
          };
          return map_cons(_tmp2);
        }());
      }
    }
    return _result;
  }

  /// scanl f acc l returns intermediate fold results.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T2 &, T1 &>
  static list<T2> scanl(F0 &&f, const T2 &acc, const list<T1> &l) {
    std::shared_ptr<list<T2>> _head{};
    std::shared_ptr<list<T2>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    T2 _loop_acc = acc;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<list<T2>>(
            list<T2>::cons(_loop_acc, list<T2>::nil()));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        T2 new_acc = f(_loop_acc, a0);
        auto _cell = std::make_shared<list<T2>>(
            typename list<T2>::Cons(_loop_acc, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<T2>::Cons>((*_write)->v_mut()).l;
        _loop_l = crane_raw(a1);
        _loop_acc = std::move(new_acc);
        continue;
      }
    }
    return std::move(*_head);
  }

  /// group_by eq l groups consecutive equal elements.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static list<list<T1>> group_by_aux(F0 &&eq, const T1 &prev,
                                     const list<T1> &acc, const list<T1> &l) {
    std::shared_ptr<list<list<T1>>> _head{};
    std::shared_ptr<list<list<T1>>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    list<T1> _loop_acc = acc;
    T1 _loop_prev = prev;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<list<list<T1>>>(
            list<list<T1>>::cons(_loop_acc, list<list<T1>>::nil()));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        if (eq(_loop_prev, a0)) {
          _loop_l = crane_raw(a1);
          _loop_acc = list<T1>::cons(a0, _loop_acc);
          _loop_prev = a0;
          continue;
        } else {
          auto _cell = std::make_shared<list<list<T1>>>(
              typename list<list<T1>>::Cons(_loop_acc, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename list<list<T1>>::Cons>((*_write)->v_mut()).l;
          _loop_l = crane_raw(a1);
          _loop_acc = list<T1>::cons(a0, list<T1>::nil());
          _loop_prev = a0;
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static list<list<T1>> group_by(F0 &&eq, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<list<T1>>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return group_by_aux<T1>(eq, a0, list<T1>::cons(a0, list<T1>::nil()), *a1);
    }
  }

  /// chunks_of n l splits into chunks of size n.
  template <typename T1>
  static list<list<T1>> chunks_of_aux(uint64_t n, const list<T1> &l,
                                      uint64_t fuel) {
    std::shared_ptr<list<list<T1>>> _head{};
    std::shared_ptr<list<list<T1>>> *_write = &_head;
    uint64_t _loop_fuel = std::move(fuel);
    list<T1> _loop_l = l;
    while (true) {
      if (_loop_fuel <= 0) {
        *_write = std::make_shared<list<list<T1>>>(list<list<T1>>::nil());
        break;
      } else {
        uint64_t f = _loop_fuel - 1;
        auto take_impl = [&](auto &, uint64_t k,
                             const list<T1> &lst) -> list<T1> {
          /// CraneEnter: captures varying parameters for each recursive call.
          struct CraneEnter {
            const list<T1> *lst;
            uint64_t k;
          };
          /// CraneCont_Cons: saves [a0], resumes after recursive call, then
          /// processes rest.
          struct CraneCont_Cons {
            T1 a0;
          };
          using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
          list<T1> _result{};
          crane::small_vector<CraneFrame> _stack;
          _stack.emplace_back(CraneEnter{&lst, k});
          /// Loopified take: CraneEnter -> CraneCont_Cons.
          while (!_stack.empty()) {
            CraneFrame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<CraneEnter>(_frame)) {
              auto _f = std::move(std::get<CraneEnter>(_frame));
              const list<T1> &lst = *_f.lst;
              uint64_t k = _f.k;
              if (k <= 0) {
                _result = list<T1>::nil();
              } else {
                uint64_t m = k - 1;
                if (std::holds_alternative<typename list<T1>::Nil>(lst.v())) {
                  _result = list<T1>::nil();
                } else {
                  const auto &[a0, a1] =
                      std::get<typename list<T1>::Cons>(lst.v());
                  _stack.emplace_back(CraneCont_Cons{a0});
                  _stack.emplace_back(CraneEnter{crane_raw(a1), m});
                }
              }
            } else {
              auto _f = std::move(std::get<CraneCont_Cons>(_frame));
              auto a0 = std::move(_f.a0);
              _result = list<T1>::cons(a0, std::move(_result));
            }
          }
          return _result;
        };
        auto take = [&](uint64_t k, const list<T1> &lst) -> list<T1> {
          return take_impl(take_impl, k, lst);
        };
        auto drop0_impl = [](auto &, uint64_t k, list<T1> lst) -> list<T1> {
          list<T1> _loop_lst = std::move(lst);
          uint64_t _loop_k = std::move(k);
          while (true) {
            if (_loop_k <= 0) {
              return _loop_lst;
            } else {
              uint64_t m = _loop_k - 1;
              if (std::holds_alternative<typename list<T1>::Nil>(
                      _loop_lst.v_mut())) {
                return list<T1>::nil();
              } else {
                auto &[a00, a10] =
                    std::get<typename list<T1>::Cons>(_loop_lst.v_mut());
                _loop_lst = list<T1>(*a10);
                _loop_k = m;
              }
            }
          }
        };
        auto drop0 = [&](uint64_t k, list<T1> lst) -> list<T1> {
          return drop0_impl(drop0_impl, k, lst);
        };
        if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
          *_write = std::make_shared<list<list<T1>>>(list<list<T1>>::nil());
          break;
        } else {
          list<T1> chunk = take(n, _loop_l);
          list<T1> rest = drop0(n, _loop_l);
          if (std::holds_alternative<typename list<T1>::Nil>(chunk.v_mut())) {
            *_write = std::make_shared<list<list<T1>>>(list<list<T1>>::nil());
            break;
          } else {
            auto _cell = std::make_shared<list<list<T1>>>(
                typename list<list<T1>>::Cons(chunk, nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename list<list<T1>>::Cons>((*_write)->v_mut()).l;
            _loop_fuel = f;
            _loop_l = std::move(rest);
            continue;
          }
        }
      }
    }
    return std::move(*_head);
  }

  template <typename T1>
  static list<list<T1>> chunks_of(uint64_t n, const list<T1> &l) {
    auto length_impl = [&](auto &, const list<T1> &l0) -> uint64_t {
      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const list<T1> *l0;
      };
      /// CraneCont_Cons: resumes after recursive call, then processes rest.
      struct CraneCont_Cons {};
      using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{&l0});
      /// Loopified length: CraneEnter -> CraneCont_Cons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const list<T1> &l0 = *_f.l0;
          if (std::holds_alternative<typename list<T1>::Nil>(l0.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l0.v());
            _stack.emplace_back(CraneCont_Cons{});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Cons>(_frame));
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    };
    auto length = [&](const list<T1> &l0) -> uint64_t {
      return length_impl(length_impl, l0);
    };
    return chunks_of_aux<T1>(n, l, (length(l) + 1));
  }

  /// step_sum l sums with conditional contributions: even values as-is, odd
  /// doubled.
  static uint64_t step_sum(const list<uint64_t> &l);
  /// sum_abs l sums absolute values (using monus for nat).
  static uint64_t sum_abs(const list<uint64_t> &l, uint64_t base);
  /// four_elem l multi-case pattern matching on list structure.
  static uint64_t four_elem(const list<uint64_t> &l);
  /// between lo hi l filters elements in range lo, hi.
  static list<uint64_t> between(uint64_t lo, uint64_t hi,
                                const list<uint64_t> &l);

  /// count_matching p l counts elements satisfying predicate.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static uint64_t count_matching(
      F0 &&p, const list<uint64_t> &l) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

    struct CraneEnter {
      const list<uint64_t> *l;
    };

    /// CraneCont1: resumes after recursive call, then processes rest.
    struct CraneCont1 {};

    using CraneFrame = std::variant<CraneEnter, CraneCont1>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified count_matching: CraneEnter -> CraneCont1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(CraneCont1{});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont1>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

  /// categorize k l categorizes elements: 1 for <k, 2 for =k, 3 for >k.
  static uint64_t categorize(uint64_t k, const list<uint64_t> &l);
  /// max_prefix_sum l maximum prefix sum (Kadane-like).
  static uint64_t max_prefix_sum(const list<uint64_t> &l);
  /// pairwise_sum l sums consecutive pairs: 1,2,3,4 -> 3,7.
  static list<uint64_t> pairwise_sum(const list<uint64_t> &l);
  /// weighted_sum i l weighted sum with increasing weights.
  static uint64_t weighted_sum(uint64_t i, const list<uint64_t> &l);

  /// zip_with f l1 l2 zips two lists with a function.
  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static list<T3> zip_with(F0 &&f, const list<T1> &l1, const list<T2> &l2) {
    std::shared_ptr<list<T3>> _head{};
    std::shared_ptr<list<T3>> *_write = &_head;
    const list<T2> *_loop_l2 = &l2;
    const list<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1->v())) {
        *_write = std::make_shared<list<T3>>(list<T3>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2->v())) {
          *_write = std::make_shared<list<T3>>(list<T3>::nil());
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename list<T2>::Cons>(_loop_l2->v());
          auto _cell = std::make_shared<list<T3>>(
              typename list<T3>::Cons(f(a0, a00), nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename list<T3>::Cons>((*_write)->v_mut()).l;
          _loop_l2 = crane_raw(a10);
          _loop_l1 = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// zip_longest l1 l2 def zips with default for mismatched lengths.
  template <typename T1>
  static list<std::pair<T1, T1>>
  zip_longest_aux(uint64_t fuel, const list<T1> &l1, const list<T1> &l2,
                  const T1 &default0) {
    std::shared_ptr<list<std::pair<T1, T1>>> _head{};
    std::shared_ptr<list<std::pair<T1, T1>>> *_write = &_head;
    list<T1> _loop_l2 = l2;
    list<T1> _loop_l1 = l1;
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        *_write = std::make_shared<list<std::pair<T1, T1>>>(
            list<std::pair<T1, T1>>::nil());
        break;
      } else {
        uint64_t f = _loop_fuel - 1;
        if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1.v())) {
          if (std::holds_alternative<typename list<T1>::Nil>(_loop_l2.v())) {
            *_write = std::make_shared<list<std::pair<T1, T1>>>(
                list<std::pair<T1, T1>>::nil());
            break;
          } else {
            const auto &[a00, a10] =
                std::get<typename list<T1>::Cons>(_loop_l2.v());
            auto _cell = std::make_shared<list<std::pair<T1, T1>>>(
                typename list<std::pair<T1, T1>>::Cons(
                    std::make_pair(default0, a00), nullptr));
            *_write = std::move(_cell);
            _write = &std::get<typename list<std::pair<T1, T1>>::Cons>(
                          (*_write)->v_mut())
                          .l;
            _loop_l2 = list<T1>(*a10);
            _loop_l1 = list<T1>::nil();
            _loop_fuel = f;
            continue;
          }
        } else {
          const auto &[a0, a1] =
              std::get<typename list<T1>::Cons>(_loop_l1.v());
          if (std::holds_alternative<typename list<T1>::Nil>(_loop_l2.v())) {
            auto _cell = std::make_shared<list<std::pair<T1, T1>>>(
                typename list<std::pair<T1, T1>>::Cons(
                    std::make_pair(a0, default0), nullptr));
            *_write = std::move(_cell);
            _write = &std::get<typename list<std::pair<T1, T1>>::Cons>(
                          (*_write)->v_mut())
                          .l;
            _loop_l2 = list<T1>::nil();
            _loop_l1 = list<T1>(*a1);
            _loop_fuel = f;
            continue;
          } else {
            const auto &[a00, a10] =
                std::get<typename list<T1>::Cons>(_loop_l2.v());
            auto _cell = std::make_shared<list<std::pair<T1, T1>>>(
                typename list<std::pair<T1, T1>>::Cons(std::make_pair(a0, a00),
                                                       nullptr));
            *_write = std::move(_cell);
            _write = &std::get<typename list<std::pair<T1, T1>>::Cons>(
                          (*_write)->v_mut())
                          .l;
            _loop_l2 = list<T1>(*a10);
            _loop_l1 = list<T1>(*a1);
            _loop_fuel = f;
            continue;
          }
        }
      }
    }
    return std::move(*_head);
  }

  template <typename T1>
  static list<std::pair<T1, T1>>
  zip_longest(const list<T1> &l1, const list<T1> &l2, const T1 &default0) {
    auto length_impl = [&](auto &, const list<T1> &l) -> uint64_t {
      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const list<T1> *l;
      };
      /// CraneCont_Cons: resumes after recursive call, then processes rest.
      struct CraneCont_Cons {};
      using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{&l});
      /// Loopified length: CraneEnter -> CraneCont_Cons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const list<T1> &l = *_f.l;
          if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
            _stack.emplace_back(CraneCont_Cons{});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Cons>(_frame));
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    };
    auto length = [&](const list<T1> &l) -> uint64_t {
      return length_impl(length_impl, l);
    };
    uint64_t len = (length(l1) + length(l2));
    return zip_longest_aux<T1>((len + 1), l1, l2, default0);
  }

  /// sliding_pairs l returns consecutive pairs: 1,2,3 -> (1,2),(2,3).
  template <typename T1>
  static list<std::pair<T1, T1>> sliding_pairs(const list<T1> &l) {
    std::shared_ptr<list<std::pair<T1, T1>>> _head{};
    std::shared_ptr<list<std::pair<T1, T1>>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<list<std::pair<T1, T1>>>(
            list<std::pair<T1, T1>>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename list<T1>::Nil>(_sv0.v())) {
          *_write = std::make_shared<list<std::pair<T1, T1>>>(
              list<std::pair<T1, T1>>::nil());
          break;
        } else {
          const auto &[a00, a10] = std::get<typename list<T1>::Cons>(_sv0.v());
          auto _cell = std::make_shared<list<std::pair<T1, T1>>>(
              typename list<std::pair<T1, T1>>::Cons(std::make_pair(a0, a00),
                                                     nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename list<std::pair<T1, T1>>::Cons>(
                        (*_write)->v_mut())
                        .l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// partition3 p q l partitions into 3 groups based on 2 predicates.
  template <typename F0, typename F1>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &> &&
             std::is_invocable_r_v<bool, F1 &, uint64_t &>
  static std::pair<std::pair<list<uint64_t>, list<uint64_t>>, list<uint64_t>>
  partition3(F0 &&p, F1 &&q,
             const list<uint64_t> &l) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

    struct CraneEnter {
      const list<uint64_t> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    std::pair<std::pair<list<uint64_t>, list<uint64_t>>, list<uint64_t>>
        _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified partition3: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = std::make_pair(
              std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil()),
              list<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        auto [p0, cs] = std::move(_result);
        auto [as_, bs] = std::move(p0);
        if (p(a0)) {
          _result = std::make_pair(
              std::make_pair(list<uint64_t>::cons(a0, std::move(as_)),
                             std::move(bs)),
              std::move(cs));
        } else {
          if (q(a0)) {
            _result = std::make_pair(
                std::make_pair(std::move(as_),
                               list<uint64_t>::cons(a0, std::move(bs))),
                std::move(cs));
          } else {
            _result =
                std::make_pair(std::make_pair(std::move(as_), std::move(bs)),
                               list<uint64_t>::cons(a0, std::move(cs)));
          }
        }
      }
    }
    return _result;
  }

  /// transpose m transposes a matrix (list of lists).
  template <typename T1>
  static list<list<T1>> transpose_fuel(uint64_t fuel, const list<list<T1>> &m) {
    std::shared_ptr<list<list<T1>>> _head{};
    std::shared_ptr<list<list<T1>>> *_write = &_head;
    list<list<T1>> _loop_m = m;
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        *_write = std::make_shared<list<list<T1>>>(list<list<T1>>::nil());
        break;
      } else {
        uint64_t f = _loop_fuel - 1;
        auto map_head_impl = [&](auto &, const list<list<T1>> &l) -> list<T1> {
          /// CraneEnter: captures varying parameters for each recursive call.
          struct CraneEnter {
            const list<list<T1>> *l;
          };
          /// CraneCont_Cons: saves [a00], resumes after recursive call, then
          /// processes rest.
          struct CraneCont_Cons {
            T1 a00;
          };
          using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
          list<T1> _result{};
          crane::small_vector<CraneFrame> _stack;
          _stack.emplace_back(CraneEnter{&l});
          /// Loopified map_head: CraneEnter -> CraneCont_Cons.
          while (!_stack.empty()) {
            CraneFrame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<CraneEnter>(_frame)) {
              auto _f = std::move(std::get<CraneEnter>(_frame));
              const list<list<T1>> &l = *_f.l;
              if (std::holds_alternative<typename list<list<T1>>::Nil>(l.v())) {
                _result = list<T1>::nil();
              } else {
                const auto &[a0, a1] =
                    std::get<typename list<list<T1>>::Cons>(l.v());
                if (std::holds_alternative<typename list<T1>::Nil>(a0.v())) {
                  _result = list<T1>::nil();
                } else {
                  const auto &[a00, a10] =
                      std::get<typename list<T1>::Cons>(a0.v());
                  _stack.emplace_back(CraneCont_Cons{a00});
                  _stack.emplace_back(CraneEnter{crane_raw(a1)});
                }
              }
            } else {
              auto _f = std::move(std::get<CraneCont_Cons>(_frame));
              auto a00 = std::move(_f.a00);
              _result = list<T1>::cons(a00, std::move(_result));
            }
          }
          return _result;
        };
        auto map_head = [&](const list<list<T1>> &l) -> list<T1> {
          return map_head_impl(map_head_impl, l);
        };
        auto map_tail_impl = [&](auto &,
                                 const list<list<T1>> &l) -> list<list<T1>> {
          /// CraneEnter: captures varying parameters for each recursive call.
          struct CraneEnter {
            const list<list<T1>> *l;
          };
          /// CraneCont_Cons: saves [a11], resumes after recursive call, then
          /// processes rest.
          struct CraneCont_Cons {
            std::shared_ptr<list<T1>> a11;
          };
          using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
          list<list<T1>> _result{};
          crane::small_vector<CraneFrame> _stack;
          _stack.emplace_back(CraneEnter{&l});
          /// Loopified map_tail: CraneEnter -> CraneCont_Cons.
          while (!_stack.empty()) {
            CraneFrame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<CraneEnter>(_frame)) {
              auto _f = std::move(std::get<CraneEnter>(_frame));
              const list<list<T1>> &l = *_f.l;
              if (std::holds_alternative<typename list<list<T1>>::Nil>(l.v())) {
                _result = list<list<T1>>::nil();
              } else {
                const auto &[a00, a10] =
                    std::get<typename list<list<T1>>::Cons>(l.v());
                if (std::holds_alternative<typename list<T1>::Nil>(a00.v())) {
                  _result = list<list<T1>>::nil();
                } else {
                  const auto &[a01, a11] =
                      std::get<typename list<T1>::Cons>(a00.v());
                  _stack.emplace_back(CraneCont_Cons{a11});
                  _stack.emplace_back(CraneEnter{crane_raw(a10)});
                }
              }
            } else {
              auto _f = std::move(std::get<CraneCont_Cons>(_frame));
              std::shared_ptr<list<T1>> a11 = std::move(_f.a11);
              _result = list<list<T1>>::cons(*a11, std::move(_result));
            }
          }
          return _result;
        };
        auto map_tail = [&](const list<list<T1>> &l) -> list<list<T1>> {
          return map_tail_impl(map_tail_impl, l);
        };
        if (std::holds_alternative<typename list<list<T1>>::Nil>(_loop_m.v())) {
          *_write = std::make_shared<list<list<T1>>>(list<list<T1>>::nil());
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename list<list<T1>>::Cons>(_loop_m.v());
          if (std::holds_alternative<typename list<T1>::Nil>(a01.v())) {
            *_write = std::make_shared<list<list<T1>>>(list<list<T1>>::nil());
            break;
          } else {
            list<T1> heads = map_head(_loop_m);
            list<list<T1>> tails0 = map_tail(_loop_m);
            if (std::holds_alternative<typename list<T1>::Nil>(heads.v_mut())) {
              *_write = std::make_shared<list<list<T1>>>(list<list<T1>>::nil());
              break;
            } else {
              auto _cell = std::make_shared<list<list<T1>>>(
                  typename list<list<T1>>::Cons(heads, nullptr));
              *_write = std::move(_cell);
              _write =
                  &std::get<typename list<list<T1>>::Cons>((*_write)->v_mut())
                       .l;
              _loop_m = std::move(tails0);
              _loop_fuel = f;
              continue;
            }
          }
        }
      }
    }
    return std::move(*_head);
  }

  template <typename T1>
  static list<list<T1>> transpose(const list<list<T1>> &m) {
    return transpose_fuel<T1>(UINT64_C(100), m);
  }

  /// map_accum_l f acc l maps with accumulator from left.
  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::pair<T3, T2>, F0 &, T3 &, T1 &>
  static std::pair<T3, list<T2>>
  map_accum_l(F0 &&f, const T3 &acc,
              const list<T1> &l) { /// CraneEnter: captures varying parameters
                                   /// for each recursive call.

    struct CraneEnter {
      const list<T1> *l;
      T3 acc;
    };

    /// CraneCont_acc_: saves [y], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_acc_ {
      T2 y;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_acc_>;
    std::pair<T3, list<T2>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l, acc});
    /// Loopified map_accum_l: CraneEnter -> CraneCont_acc_.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<T1> &l = *_f.l;
        const T3 acc = std::move(_f.acc);
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::make_pair(acc, list<T2>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          auto [acc_, y] = f(acc, a0);
          _stack.emplace_back(CraneCont_acc_{y});
          _stack.emplace_back(CraneEnter{crane_raw(a1), acc_});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_acc_>(_frame));
        auto y = std::move(_f.y);
        auto [acc_p, ys] = std::move(_result);
        _result = std::make_pair(acc_p, list<T2>::cons(y, std::move(ys)));
      }
    }
    return _result;
  }

  /// prefix_sums acc l returns all prefix sums: 1,2,3 -> 0,1,3,6.
  static list<uint64_t> prefix_sums(uint64_t acc, const list<uint64_t> &l);
  /// uniq_sorted l removes consecutive duplicates from sorted list.
  static list<uint64_t> uniq_sorted(const list<uint64_t> &l);
  /// Helper: take first n elements.
  static list<uint64_t> take_n(uint64_t n, const list<uint64_t> &l);
  /// Helper: list length.
  static uint64_t len_list(const list<uint64_t> &l);
  /// windows n l returns all sliding windows of size n.
  static list<list<uint64_t>> windows_aux(uint64_t fuel, uint64_t n,
                                          const list<uint64_t> &l);
  static list<list<uint64_t>> windows(uint64_t n, const list<uint64_t> &l);
  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  static bool is_prefix_of(const list<uint64_t> &l1, const list<uint64_t> &l2);
  /// lookup_all key l finds all values for key in association list.
  static list<uint64_t>
  lookup_all(uint64_t key, const list<std::pair<uint64_t, uint64_t>> &l);

  /// delete_by eq x l deletes first element equal to x by custom equality.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &, uint64_t &>
  static list<uint64_t> delete_by(F0 &&eq, uint64_t x,
                                  const list<uint64_t> &l) {
    std::shared_ptr<list<uint64_t>> _head{};
    std::shared_ptr<list<uint64_t>> *_write = &_head;
    const list<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<list<uint64_t>>(list<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename list<uint64_t>::Cons>(_loop_l->v());
        if (eq(x, a0)) {
          *_write = std::make_shared<list<uint64_t>>(*a1);
          break;
        } else {
          auto _cell = std::make_shared<list<uint64_t>>(
              typename list<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// find_indices p l returns list of indices where predicate holds.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static list<uint64_t> find_indices_aux(F0 &&p, const list<uint64_t> &l,
                                         uint64_t i) {
    std::shared_ptr<list<uint64_t>> _head{};
    std::shared_ptr<list<uint64_t>> *_write = &_head;
    uint64_t _loop_i = std::move(i);
    const list<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<list<uint64_t>>(list<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename list<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = std::make_shared<list<uint64_t>>(
              typename list<uint64_t>::Cons(_loop_i, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).l;
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
    return std::move(*_head);
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static list<uint64_t> find_indices(F0 &&p, const list<uint64_t> &l) {
    return find_indices_aux(p, l, UINT64_C(0));
  }

  /// member x l checks if x is in the list.
  static bool member(uint64_t x, const list<uint64_t> &l);
  /// product l multiplies all elements in the list.
  static uint64_t product(const list<uint64_t> &l);
  /// sum_list l sums all elements in the list.
  static uint64_t sum_list(const list<uint64_t> &l);

  /// flatten l flattens a list of lists.
  template <typename T1>
  static list<T1>
  flatten(const list<list<T1>> &l) { /// CraneEnter: captures varying parameters
                                     /// for each recursive call.

    struct CraneEnter {
      const list<list<T1>> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      list<T1> a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    list<T1> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified flatten: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<list<T1>> &l = *_f.l;
        if (std::holds_alternative<typename list<list<T1>>::Nil>(l.v())) {
          _result = list<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<list<T1>>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        list<T1> a0 = std::move(_f.a0);
        list<T1> _tmp2 = std::move(_result);
        auto app_impl = [&](auto &, const list<T1> &l1,
                            list<T1> l2) -> list<T1> {
          /// CraneEnter: captures varying parameters for each recursive call.
          struct CraneEnter {
            list<T1> l2;
            const list<T1> *l1;
          };
          /// CraneCont_Cons: saves [a00], resumes after recursive call, then
          /// processes rest.
          struct CraneCont_Cons {
            T1 a00;
          };
          using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
          list<T1> _result{};
          crane::small_vector<CraneFrame> _stack;
          _stack.emplace_back(CraneEnter{std::move(l2), &l1});
          /// Loopified app: CraneEnter -> CraneCont_Cons.
          while (!_stack.empty()) {
            CraneFrame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<CraneEnter>(_frame)) {
              auto _f = std::move(std::get<CraneEnter>(_frame));
              list<T1> l2 = std::move(_f.l2);
              const list<T1> &l1 = *_f.l1;
              if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
                _result = std::move(l2);
              } else {
                const auto &[a00, a10] =
                    std::get<typename list<T1>::Cons>(l1.v());
                _stack.emplace_back(CraneCont_Cons{a00});
                _stack.emplace_back(CraneEnter{std::move(l2), crane_raw(a10)});
              }
            } else {
              auto _f = std::move(std::get<CraneCont_Cons>(_frame));
              auto a00 = std::move(_f.a00);
              _result = list<T1>::cons(a00, std::move(_result));
            }
          }
          return _result;
        };
        auto app = [&](const list<T1> &l1, list<T1> l2) -> list<T1> {
          return app_impl(app_impl, l1, l2);
        };
        _result = app(a0, std::move(_tmp2));
      }
    }
    return _result;
  }

  /// flatten_nested l alternative flatten with different pattern: flattens one
  /// level at a time. Pattern:  :: rest -> flatten rest, (x :: xs) :: rest -> x
  /// :: flatten (xs :: rest).
  static list<uint64_t> flatten_nested_fuel(uint64_t fuel,
                                            const list<list<uint64_t>> &l);
  static uint64_t sum_list_lengths(const list<list<uint64_t>> &l);
  static list<uint64_t> flatten_nested(const list<list<uint64_t>> &l);
  /// compress l removes consecutive duplicates: 1,1,2,2,2,3 -> 1,2,3.
  static list<uint64_t> compress(const list<uint64_t> &l);
  /// group_pairs l groups consecutive elements into pairs: 1,2,3,4 ->
  /// (1,2),(3,4).
  static list<std::pair<uint64_t, uint64_t>>
  group_pairs(const list<uint64_t> &l);
  /// swizzle l separates elements by position: 1,2,3,4 -> (1,3,2,4).
  static std::pair<list<uint64_t>, list<uint64_t>>
  swizzle(const list<uint64_t> &l);
  /// index_of_aux x l i finds first index of x in l starting from i.
  static uint64_t index_of_aux(uint64_t x, const list<uint64_t> &l, uint64_t i);
  static uint64_t index_of(uint64_t x, const list<uint64_t> &l);
  /// interleave l1 l2 interleaves two lists: 1,2 3,4 -> 1,3,2,4.
  static list<uint64_t> interleave(list<uint64_t> l1, list<uint64_t> l2);
  /// lookup key l finds value for key in association list.
  static uint64_t lookup(uint64_t key,
                         const list<std::pair<uint64_t, uint64_t>> &l);
  /// group l groups consecutive equal elements: 1,1,2,2,2,3 ->
  /// [1,1],[2,2,2],[3].
  static list<list<uint64_t>> group_fuel(uint64_t fuel,
                                         const list<uint64_t> &l);
  static list<list<uint64_t>> group(const list<uint64_t> &l);
  /// Internal helper: reverse a list.
  static list<uint64_t> rev_helper(list<uint64_t> acc, const list<uint64_t> &l);
  /// reverse_insert x l inserts x and reverses at each step.
  static list<uint64_t> reverse_insert(uint64_t x, const list<uint64_t> &l);
  /// Internal helper: append lists.
  static list<uint64_t> app_helper(const list<uint64_t> &l1, list<uint64_t> l2);
  /// double_append l1 l2 appends with doubling: 1,2 3 -> 1,3,3,3,3.
  static list<uint64_t> double_append(const list<uint64_t> &l1,
                                      list<uint64_t> l2);
  /// remove_if_sum_even l removes element if sum with next is even.
  static list<uint64_t> remove_if_sum_even(const list<uint64_t> &l);
  /// split_at n l splits list at index n into (prefix, suffix).
  static std::pair<list<uint64_t>, list<uint64_t>>
  split_at(uint64_t n, const list<uint64_t> &l);

  /// span p l splits list at first element not satisfying p.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static std::pair<list<uint64_t>, list<uint64_t>>
  span(F0 &&p,
       const list<uint64_t> &l) { /// CraneEnter: captures varying parameters
                                  /// for each recursive call.

    struct CraneEnter {
      const list<uint64_t> *l;
    };

    /// CraneCont1: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont1 {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont1>;
    std::pair<list<uint64_t>, list<uint64_t>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified span: CraneEnter -> CraneCont1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result =
              std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(CraneCont1{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            _result = std::make_pair(list<uint64_t>::nil(), l);
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont1>(_frame));
        uint64_t a0 = _f.a0;
        auto [a, b] = std::move(_result);
        _result = std::make_pair(list<uint64_t>::cons(a0, std::move(a)),
                                 std::move(b));
      }
    }
    return _result;
  }

  /// unzip l splits list of pairs into two lists.
  static std::pair<list<uint64_t>, list<uint64_t>>
  unzip(const list<std::pair<uint64_t, uint64_t>> &l);
  /// nth n l default returns nth element or default if out of bounds.
  static uint64_t nth(uint64_t n, const list<uint64_t> &l, uint64_t default0);
  /// last l default returns last element or default if empty.
  static uint64_t last(const list<uint64_t> &l, uint64_t default0);
  /// drop n l drops first n elements.
  static list<uint64_t> drop(uint64_t n, list<uint64_t> l);
  /// init l returns all but last element.
  static list<uint64_t> init(const list<uint64_t> &l);
  /// count x l counts occurrences of x in l.
  static uint64_t count(uint64_t x, const list<uint64_t> &l);
  /// maximum l finds maximum element (returns 0 for empty list).
  static uint64_t maximum(const list<uint64_t> &l);
  /// minmax l finds both minimum and maximum in one pass.
  static std::pair<uint64_t, uint64_t> minmax(const list<uint64_t> &l);
  /// Helper for rotate_left.
  static list<uint64_t> rotate_left_fuel(uint64_t fuel, uint64_t n,
                                         list<uint64_t> l);
  /// rotate_left n l rotates list left by n positions: rotate 2 1,2,3,4 ->
  /// 3,4,1,2.
  static list<uint64_t> rotate_left(uint64_t n, const list<uint64_t> &l);
  /// intercalate sep lists joins lists with separator: intercalate 0
  /// [1,2],[3,4] -> 1,2,0,3,4.
  static list<uint64_t> intercalate(const list<uint64_t> &sep,
                                    const list<list<uint64_t>> &lists);
  /// majority l finds majority element using Boyer-Moore voting algorithm.
  /// Returns (candidate, count).
  static std::pair<uint64_t, uint64_t> majority(const list<uint64_t> &l);
  /// zip3 l1 l2 l3 zips three lists into triples.
  static list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>
  zip3(const list<uint64_t> &l1, const list<uint64_t> &l2,
       const list<uint64_t> &l3);
  /// sum_and_count l returns both sum and count in one pass.
  static std::pair<uint64_t, uint64_t> sum_and_count(const list<uint64_t> &l);
  /// elem_at n l returns element at index n (like nth but with different name).
  static std::optional<uint64_t> elem_at(uint64_t n, const list<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_LISTS
