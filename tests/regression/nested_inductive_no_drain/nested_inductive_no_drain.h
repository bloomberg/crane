#ifndef INCLUDED_NESTED_INDUCTIVE_NO_DRAIN
#define INCLUDED_NESTED_INDUCTIVE_NO_DRAIN

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct NestedInductiveNoDrain {
  template <typename A> struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::shared_ptr<lst<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    lst() {}

    explicit lst(Nil _v) : v_(_v) {}

    explicit lst(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    lst(const lst<CraneU> &_other)
        : v_(crane_convert_spine(
              _other, std::shared_ptr<lst<A>>(nullptr),
              [](const lst<CraneU> &_cell) -> const lst<CraneU> * {
                if (std::holds_alternative<typename lst<CraneU>::Cons>(
                        _cell.v())) {
                  return std::get<typename lst<CraneU>::Cons>(_cell.v())
                      .a1.get();
                } else {
                  return nullptr;
                }
              },
              [&](const lst<CraneU> &_other,
                  std::shared_ptr<lst<A>> _below) -> variant_t {
                if (std::holds_alternative<typename lst<CraneU>::Nil>(
                        _other.v())) {
                  return Nil{};
                } else {
                  const auto &[a0, a1] =
                      std::get<typename lst<CraneU>::Cons>(_other.v());
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
                      std::move(_below)};
                }
              },
              [](auto &&_alt) {
                return std::make_shared<lst<A>>(std::move(_alt));
              })) {}

    static lst<A> nil() { return lst<A>(Nil{}); }

    static lst<A> cons(A a0, lst<A> a1) {
      return lst<A>(
          Cons{std::move(a0), std::make_shared<lst<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<lst<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<lst<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    lst(const lst &) = default;
    lst &operator=(const lst &) = default;
    lst(lst &&) = default;
    lst &operator=(lst &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1> T1 lst_rec(T1 f, F1 &&f0) const {
      const lst<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const lst<A> *_self;
      };

      /// CraneCont_Cons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cons {
        A a0;
        std::shared_ptr<lst<A>> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified lst_rec: CraneEnter -> CraneCont_Cons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const lst<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename lst<A>::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename lst<A>::Cons>(_sv.v());
            _stack.emplace_back(CraneCont_Cons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Cons>(_frame));
          auto a0 = std::move(_f.a0);
          std::shared_ptr<lst<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 lst_rect(T1 f, F1 &&f0) const {
      const lst<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const lst<A> *_self;
      };

      /// CraneCont_Cons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cons {
        A a0;
        std::shared_ptr<lst<A>> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified lst_rect: CraneEnter -> CraneCont_Cons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const lst<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename lst<A>::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename lst<A>::Cons>(_sv.v());
            _stack.emplace_back(CraneCont_Cons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Cons>(_frame));
          auto a0 = std::move(_f.a0);
          std::shared_ptr<lst<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct tree {
    // TYPES
    struct Node {
      uint64_t a0;
      std::shared_ptr<lst<tree>> a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree node(uint64_t a0, lst<tree> a1) {
      return tree(Node{a0, std::make_shared<lst<tree>>(std::move(a1))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto _lp = _alt->a1.get();
            while (std::holds_alternative<typename lst<tree>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename lst<tree>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<tree>(std::move(_lc.a0)));
              if (_lc.a1 && _lc.a1.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.a1.get();
              } else {
                break;
              }
            }
            _alt->a1.reset();
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

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t tsum() const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      using CraneFrame = std::variant<CraneEnter>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tsum: CraneEnter.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const tree *_self = _f._self;
        auto &&_sv = *_self;
        const auto &[a0, a1] = std::get<typename tree::Node>(_sv.v());
        uint64_t _tmp3;
        auto go0_impl = [](auto &_self_go0, const lst<tree> &m) -> uint64_t {
          if (std::holds_alternative<typename lst<tree>::Nil>(m.v())) {
            return UINT64_C(0);
          } else {
            const auto &[a00, a10] = std::get<typename lst<tree>::Cons>(m.v());
            return (a00.tsum() + _self_go0(_self_go0, *a10));
          }
        };
        auto go0 = [&](const lst<tree> &m) -> uint64_t {
          return go0_impl(go0_impl, m);
        };
        _tmp3 = go0(*a1);
        _result = (a0 + _tmp3);
      }
      return _result;
    }

    tree spine(uint64_t n) const {
      tree _self_store;
      const tree *_loop_self = this;
      uint64_t _loop_n = n;
      while (true) {
        if (_loop_n <= 0) {
          return std::move(*_loop_self);
        } else {
          uint64_t m = _loop_n - 1;
          _self_store =
              tree::node(_loop_n, lst<tree>::cons(std::move(*_loop_self),
                                                  lst<tree>::nil()));
          _loop_self = &_self_store;
          _loop_n = m;
        }
      }
    }

    template <typename T1, typename F0> T1 tree_rec(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
      return f(a0, *a1);
    }

    template <typename T1, typename F0> T1 tree_rect(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
      return f(a0, *a1);
    }
  };

  static uint64_t go(uint64_t n);
};

#endif // INCLUDED_NESTED_INDUCTIVE_NO_DRAIN
