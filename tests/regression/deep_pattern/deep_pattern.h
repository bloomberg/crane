#ifndef INCLUDED_DEEP_PATTERN
#define INCLUDED_DEEP_PATTERN

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct DeepPattern {
  struct tree {
    // TYPES
    struct Leaf {
      uint64_t a0;
    };

    struct Node {
      std::shared_ptr<tree> a0;
      std::shared_ptr<tree> a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(std::move(_v)) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree leaf(uint64_t a0) { return tree(Leaf{a0}); }

    static tree node(tree a0, tree a1) {
      return tree(Node{std::make_shared<tree>(std::move(a0)),
                       std::make_shared<tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
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

    uint64_t nested_let_match() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename tree::Leaf>(this->v());
        return a0;
      } else {
        const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
        uint64_t a = [&]() {
          auto &&_sv0 = *a0;
          if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
            const auto &[a00] = std::get<typename tree::Leaf>(_sv0.v());
            return a00;
          } else {
            return UINT64_C(0);
          }
        }();
        uint64_t b = [&]() {
          auto &&_sv1 = *a1;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[a01] = std::get<typename tree::Leaf>(_sv1.v());
            return a01;
          } else {
            return UINT64_C(0);
          }
        }();
        uint64_t c = (a + b);
        uint64_t d = (c * UINT64_C(2));
        return (d + UINT64_C(1));
      }
    }

    uint64_t conditional_match(uint64_t target) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename tree::Leaf>(this->v());
        if (a0 == target) {
          return UINT64_C(100);
        } else {
          return a0;
        }
      } else {
        const auto &[a0, _] = std::get<typename tree::Node>(this->v());
        if (this->has_value(target)) {
          return UINT64_C(200);
        } else {
          auto &&_sv0 = *a0;
          if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
            const auto &[a00] = std::get<typename tree::Leaf>(_sv0.v());
            return a00;
          } else {
            return UINT64_C(0);
          }
        }
      }
    }

    bool has_value(uint64_t target) const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of has_value: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_has_value_in_Node {
        const tree *a1;
      };

      struct _after_has_value_in_Node_2 {
        bool _tmp2;
      };

      using _frame = std::variant<_call, _after_has_value_in_Node,
                                  _after_has_value_in_Node_2>;
      bool _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            const auto &[a0] = std::get<typename tree::Leaf>(_sv.v());
            _result = a0 == target;
          } else {
            const auto &[a0, a1] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_has_value_in_Node{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_has_value_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_has_value_in_Node>(_popped));
          _stack.pop_back();
          const tree &a1 = *_f.a1;
          _stack.emplace_back(_after_has_value_in_Node_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_has_value_in_Node_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp2 || std::move(_result));
        }
      }
      return _result;
    }

    tree as_pattern_test() const { return *this; }

    uint64_t wildcard_with_bindings() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename tree::Leaf>(this->v());
        return a0;
      } else {
        const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
        uint64_t x = [&]() {
          auto &&_sv0 = *a0;
          if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
            const auto &[a00] = std::get<typename tree::Leaf>(_sv0.v());
            return a00;
          } else {
            return UINT64_C(0);
          }
        }();
        uint64_t y = [&]() {
          auto &&_sv1 = *a1;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[a01] = std::get<typename tree::Leaf>(_sv1.v());
            return a01;
          } else {
            return UINT64_C(0);
          }
        }();
        return (x + y);
      }
    }

    uint64_t multi_constructor(const tree &t2) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename tree::Leaf>(this->v());
        if (std::holds_alternative<typename tree::Leaf>(t2.v())) {
          const auto &[a00] = std::get<typename tree::Leaf>(t2.v());
          return (a0 + a00);
        } else {
          const auto &[a00, _] = std::get<typename tree::Node>(t2.v());
          auto &&_sv1 = *a00;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[a01] = std::get<typename tree::Leaf>(_sv1.v());
            return (a0 + a01);
          } else {
            return UINT64_C(0);
          }
        }
      } else {
        const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          const auto &[a00] = std::get<typename tree::Leaf>(_sv0.v());
          auto &&_sv1 = *a1;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[a01] = std::get<typename tree::Leaf>(_sv1.v());
            if (std::holds_alternative<typename tree::Leaf>(t2.v())) {
              const auto &[a02] = std::get<typename tree::Leaf>(t2.v());
              return (a00 + a02);
            } else {
              const auto &[a02, a12] = std::get<typename tree::Node>(t2.v());
              auto &&_sv3 = *a02;
              if (std::holds_alternative<typename tree::Leaf>(_sv3.v())) {
                const auto &[a03] = std::get<typename tree::Leaf>(_sv3.v());
                auto &&_sv4 = *a12;
                if (std::holds_alternative<typename tree::Leaf>(_sv4.v())) {
                  const auto &[a04] = std::get<typename tree::Leaf>(_sv4.v());
                  return (((a00 + a01) + a03) + a04);
                } else {
                  return UINT64_C(0);
                }
              } else {
                return UINT64_C(0);
              }
            }
          } else {
            if (std::holds_alternative<typename tree::Leaf>(t2.v())) {
              const auto &[a02] = std::get<typename tree::Leaf>(t2.v());
              return (a00 + a02);
            } else {
              return UINT64_C(0);
            }
          }
        } else {
          return UINT64_C(0);
        }
      }
    }

    uint64_t deep_match() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename tree::Leaf>(this->v());
        return a0;
      } else {
        const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          const auto &[a00] = std::get<typename tree::Leaf>(_sv0.v());
          auto &&_sv1 = *a1;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[a01] = std::get<typename tree::Leaf>(_sv1.v());
            return (a00 + a01);
          } else {
            const auto &[a01, a11] = std::get<typename tree::Node>(_sv1.v());
            auto &&_sv2 = *a01;
            if (std::holds_alternative<typename tree::Leaf>(_sv2.v())) {
              const auto &[a02] = std::get<typename tree::Leaf>(_sv2.v());
              auto &&_sv3 = *a11;
              if (std::holds_alternative<typename tree::Leaf>(_sv3.v())) {
                const auto &[a03] = std::get<typename tree::Leaf>(_sv3.v());
                return ((a00 + a02) + a03);
              } else {
                return UINT64_C(0);
              }
            } else {
              return UINT64_C(0);
            }
          }
        } else {
          const auto &[a00, a10] = std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *a00;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[a01] = std::get<typename tree::Leaf>(_sv1.v());
            auto &&_sv2 = *a10;
            if (std::holds_alternative<typename tree::Leaf>(_sv2.v())) {
              const auto &[a02] = std::get<typename tree::Leaf>(_sv2.v());
              auto &&_sv3 = *a1;
              if (std::holds_alternative<typename tree::Leaf>(_sv3.v())) {
                const auto &[a03] = std::get<typename tree::Leaf>(_sv3.v());
                return ((a01 + a02) + a03);
              } else {
                const auto &[a03, a13] =
                    std::get<typename tree::Node>(_sv3.v());
                auto &&_sv4 = *a03;
                if (std::holds_alternative<typename tree::Leaf>(_sv4.v())) {
                  const auto &[a04] = std::get<typename tree::Leaf>(_sv4.v());
                  auto &&_sv5 = *a13;
                  if (std::holds_alternative<typename tree::Leaf>(_sv5.v())) {
                    const auto &[a05] = std::get<typename tree::Leaf>(_sv5.v());
                    return (((a01 + a02) + a04) + a05);
                  } else {
                    return UINT64_C(0);
                  }
                } else {
                  return UINT64_C(0);
                }
              }
            } else {
              return UINT64_C(0);
            }
          } else {
            const auto &[a01, a11] = std::get<typename tree::Node>(_sv1.v());
            auto &&_sv2 = *a01;
            if (std::holds_alternative<typename tree::Leaf>(_sv2.v())) {
              const auto &[a02] = std::get<typename tree::Leaf>(_sv2.v());
              auto &&_sv3 = *a11;
              if (std::holds_alternative<typename tree::Leaf>(_sv3.v())) {
                const auto &[a03] = std::get<typename tree::Leaf>(_sv3.v());
                auto &&_sv4 = *a10;
                if (std::holds_alternative<typename tree::Leaf>(_sv4.v())) {
                  const auto &[a04] = std::get<typename tree::Leaf>(_sv4.v());
                  auto &&_sv5 = *a1;
                  if (std::holds_alternative<typename tree::Leaf>(_sv5.v())) {
                    const auto &[a05] = std::get<typename tree::Leaf>(_sv5.v());
                    return (((a02 + a03) + a04) + a05);
                  } else {
                    return UINT64_C(0);
                  }
                } else {
                  return UINT64_C(0);
                }
              } else {
                return UINT64_C(0);
              }
            } else {
              return UINT64_C(0);
            }
          }
        }
      }
    }

    template <typename T1, typename F0, typename F1>
    T1 tree_rec(F0 &&f, F1 &&f0) const {
      return this->template tree_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 tree_rect(F0 &&f, F1 &&f0) const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of tree_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_tree_rect_in_Node {
        std::shared_ptr<tree> a0;
        const tree *a1;
      };

      struct _after_tree_rect_in_Node_2 {
        std::shared_ptr<tree> a0;
        const tree *a1;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_tree_rect_in_Node,
                                  _after_tree_rect_in_Node_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            const auto &[a0] = std::get<typename tree::Leaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_tree_rect_in_Node{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_tree_rect_in_Node>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          const tree &a1 = *_f.a1;
          _stack.emplace_back(_after_tree_rect_in_Node_2{std::move(a0), &a1,
                                                         std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_tree_rect_in_Node_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          const tree &a1 = *_f.a1;
          _result = f0(*a0, std::move(_f._tmp2), a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::shared_ptr<list<A>> a1;
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
            if (std::holds_alternative<typename list<CraneU>::Nil>(_other.v())) {
              return Nil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename list<CraneU>::Cons>(_other.v());
              return Cons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<list<A>>(crane_convert<list<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static list<A> nil() { return list<A>(Nil{}); }

    static list<A> cons(A a0, list<A> a1) {
      return list<A>(
          Cons{std::move(a0), std::make_shared<list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<list<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
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

    template <typename T1, typename F1> T1 list_rec(T1 f, F1 &&f0) const {
      return this->template list_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 list_rect(T1 f, F1 &&f0) const {
      const list<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of list_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const list<A> *_self;
      };

      struct _after_list_rect_in_Cons {
        A a0;
        std::shared_ptr<list<A>> a1;
      };

      using _frame = std::variant<_call, _after_list_rect_in_Cons>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const list<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list<A>::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename list<A>::Cons>(_sv.v());
            _stack.emplace_back(_after_list_rect_in_Cons{a0, a1});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_after_list_rect_in_Cons>(_popped));
          _stack.pop_back();
          auto a0 = std::move(_f.a0);
          std::shared_ptr<list<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  static uint64_t list_deep_match(const list<tree> &l);
  static inline const uint64_t test1 =
      tree::node(tree::leaf(UINT64_C(1)), tree::leaf(UINT64_C(2))).deep_match();
  static inline const uint64_t test2 =
      tree::leaf(UINT64_C(5)).multi_constructor(tree::leaf(UINT64_C(10)));
};

#endif // INCLUDED_DEEP_PATTERN
