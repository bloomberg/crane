#ifndef INCLUDED_NESTED_IND
#define INCLUDED_NESTED_IND

#include "crane_fn.h"
#include "small_vector.h"
#include <algorithm>
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
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

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
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

struct NestedInd {
  template <typename A> struct custom_list {
    // TYPES
    struct Cnil {};

    struct Ccons {
      A a0;
      std::shared_ptr<custom_list<A>> a1;
    };

    using variant_t = std::variant<Cnil, Ccons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    custom_list() {}

    explicit custom_list(Cnil _v) : v_(_v) {}

    explicit custom_list(Ccons _v) : v_(std::move(_v)) {}

    template <typename _U> custom_list(const custom_list<_U> &_other) {
      if (std::holds_alternative<typename custom_list<_U>::Cnil>(_other.v())) {
        this->v_ = Cnil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename custom_list<_U>::Ccons>(_other.v());
        this->v_ = Ccons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<custom_list<A>>(*a1) : nullptr};
      }
    }

    static custom_list<A> cnil() { return custom_list<A>(Cnil{}); }

    static custom_list<A> ccons(A a0, custom_list<A> a1) {
      return custom_list<A>(Ccons{
          std::move(a0), std::make_shared<custom_list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~custom_list() {
      crane::small_vector<std::shared_ptr<custom_list<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Ccons>(&_v)) {
          if (_alt->a1) {
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

    custom_list(const custom_list &) = default;
    custom_list &operator=(const custom_list &) = default;
    custom_list(custom_list &&) noexcept = default;
    custom_list &operator=(custom_list &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t custom_list_length() const {
      const custom_list *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const custom_list *_self;
      };

      /// _Resume_Ccons: saves [_s0], resumes after recursive call with _result.
      struct _Resume_Ccons {
        std::decay_t<decltype(UINT64_C(1))> _s0;
      };

      using _Frame = std::variant<_Enter, _Resume_Ccons>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified custom_list_length: _Enter -> _Resume_Ccons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const custom_list *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename custom_list<A>::Cnil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] =
                std::get<typename custom_list<A>::Ccons>(_sv.v());
            _stack.emplace_back(_Resume_Ccons{UINT64_C(1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Ccons>(_frame));
          _result = (_f._s0 + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, custom_list<A> &, T1 &>
    T1 custom_list_rec(T1 f, F1 &&f0) const {
      const custom_list *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const custom_list *_self;
      };

      /// _Resume_Ccons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Ccons {
        custom_list<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Ccons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified custom_list_rec: _Enter -> _Resume_Ccons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const custom_list *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename custom_list<A>::Cnil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename custom_list<A>::Ccons>(_sv.v());
            _stack.emplace_back(_Resume_Ccons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Ccons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, custom_list<A> &, T1 &>
    T1 custom_list_rect(T1 f, F1 &&f0) const {
      const custom_list *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const custom_list *_self;
      };

      /// _Resume_Ccons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Ccons {
        custom_list<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Ccons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified custom_list_rect: _Enter -> _Resume_Ccons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const custom_list *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename custom_list<A>::Cnil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename custom_list<A>::Ccons>(_sv.v());
            _stack.emplace_back(_Resume_Ccons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Ccons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }
  };

  template <typename A> struct rose {
    // TYPES
    struct Node {
      A a0;
      std::shared_ptr<custom_list<rose<A>>> a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(Node _v) : v_(std::move(_v)) {}

    template <typename _U> rose(const rose<_U> &_other) {
      const auto &[a0, a1] = std::get<typename rose<_U>::Node>(_other.v());
      this->v_ = Node{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a0.type() == typeid(A))
                return std::any_cast<A>(a0);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a0);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a0);
            } else
              return A(a0);
          }(),
          a1 ? std::make_shared<custom_list<rose<A>>>(*a1) : nullptr};
    }

    static rose<A> node(A a0, custom_list<rose<A>> a1) {
      return rose<A>(Node{std::move(a0), std::make_shared<custom_list<rose<A>>>(
                                             std::move(a1))});
    }

    // MANIPULATORS
    ~rose() {
      crane::small_vector<std::shared_ptr<rose<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto *_lp = _alt->a1.get();
            while (std::holds_alternative<
                   typename NestedInd::custom_list<rose<A>>::Ccons>(_lp->v())) {
              auto &_lc =
                  std::get<typename NestedInd::custom_list<rose<A>>::Ccons>(
                      _lp->v_mut());
              _stack.push_back(std::make_shared<rose<A>>(std::move(_lc.a0)));
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

    rose(const rose &) = default;
    rose &operator=(const rose &) = default;
    rose(rose &&) noexcept = default;
    rose &operator=(rose &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t children_count() const {
      const auto &[a0, a1] = std::get<typename rose<A>::Node>(this->v());
      return a1->custom_list_length();
    }

    A root() const {
      const auto &[a0, a1] = std::get<typename rose<A>::Node>(this->v());
      return a0;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, custom_list<rose<A>> &>
    T1 rose_rec(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose<A>::Node>(this->v());
      return f(a0, *a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, custom_list<rose<A>> &>
    T1 rose_rect(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose<A>::Node>(this->v());
      return f(a0, *a1);
    }
  };

  static rose<uint64_t> leaf(uint64_t n);
  static inline const rose<uint64_t> small_tree = rose<uint64_t>::node(
      UINT64_C(1),
      custom_list<rose<uint64_t>>::ccons(
          leaf(UINT64_C(2)),
          custom_list<rose<uint64_t>>::ccons(
              leaf(UINT64_C(3)), custom_list<rose<uint64_t>>::cnil())));
  static inline const rose<uint64_t> bigger_tree = rose<uint64_t>::node(
      UINT64_C(1), custom_list<rose<uint64_t>>::ccons(
                       small_tree, custom_list<rose<uint64_t>>::ccons(
                                       leaf(UINT64_C(4)),
                                       custom_list<rose<uint64_t>>::cnil())));
  static inline const uint64_t test_root_leaf = leaf(UINT64_C(5)).root();
  static inline const uint64_t test_root_small = small_tree.root();
  static inline const uint64_t test_children_leaf =
      leaf(UINT64_C(5)).children_count();
  static inline const uint64_t test_children_small =
      small_tree.children_count();
  static inline const uint64_t test_children_bigger =
      bigger_tree.children_count();

  struct expr {
    // TYPES
    struct Lit {
      uint64_t a0;
    };

    struct Add {
      std::shared_ptr<List<expr>> a0;
    };

    struct Mul {
      std::shared_ptr<List<expr>> a0;
    };

    using variant_t = std::variant<Lit, Add, Mul>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : v_(std::move(_v)) {}

    explicit expr(Add _v) : v_(std::move(_v)) {}

    explicit expr(Mul _v) : v_(std::move(_v)) {}

    static expr lit(uint64_t a0) { return expr(Lit{a0}); }

    static expr add(List<expr> a0) {
      return expr(Add{std::make_shared<List<expr>>(std::move(a0))});
    }

    static expr mul(List<expr> a0) {
      return expr(Mul{std::make_shared<List<expr>>(std::move(a0))});
    }

    // MANIPULATORS
    ~expr() {
      crane::small_vector<std::shared_ptr<expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Add>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto *_lp = _alt->a0.get();
            while (
                std::holds_alternative<typename List<expr>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<expr>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<expr>(std::move(_lc.a)));
              if (_lc.l && _lc.l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->a0.reset();
          }
        }
        if (auto *_alt = std::get_if<Mul>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto *_lp = _alt->a0.get();
            while (
                std::holds_alternative<typename List<expr>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<expr>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<expr>(std::move(_lc.a)));
              if (_lc.l && _lc.l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->a0.reset();
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

    expr(const expr &) = default;
    expr &operator=(const expr &) = default;
    expr(expr &&) noexcept = default;
    expr &operator=(expr &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
    expr lit_map(F0 &&f) const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      using _Frame = std::variant<_Enter>;
      expr _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified lit_map: _Enter.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        auto _f = std::move(std::get<_Enter>(_frame));
        const expr *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
          const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
          _result = expr::lit(f(a0));
        } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
          const auto &[a0] = std::get<typename expr::Add>(_sv.v());
          auto aux_impl = [&](auto &_self_aux,
                              const List<expr> &l) -> List<expr> {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return List<expr>::nil();
            } else {
              const auto &[a1, a2] = std::get<typename List<expr>::Cons>(l.v());
              return List<expr>::cons(a1.lit_map(f), _self_aux(_self_aux, *a2));
            }
          };
          auto aux = [&](const List<expr> &l) -> List<expr> {
            return aux_impl(aux_impl, l);
          };
          _result = expr::add(aux(*a0));
        } else {
          const auto &[a0] = std::get<typename expr::Mul>(_sv.v());
          auto aux_impl = [&](auto &_self_aux,
                              const List<expr> &l) -> List<expr> {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return List<expr>::nil();
            } else {
              const auto &[a1, a2] = std::get<typename List<expr>::Cons>(l.v());
              return List<expr>::cons(a1.lit_map(f), _self_aux(_self_aux, *a2));
            }
          };
          auto aux = [&](const List<expr> &l) -> List<expr> {
            return aux_impl(aux_impl, l);
          };
          _result = expr::mul(aux(*a0));
        }
      }
      return _result;
    }

    List<uint64_t> literals() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      using _Frame = std::variant<_Enter>;
      List<uint64_t> _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified literals: _Enter.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        auto _f = std::move(std::get<_Enter>(_frame));
        const expr *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
          const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
          _result = List<uint64_t>::cons(a0, List<uint64_t>::nil());
        } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
          const auto &[a0] = std::get<typename expr::Add>(_sv.v());
          auto aux_impl = [](auto &_self_aux,
                             const List<expr> &l) -> List<uint64_t> {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return List<uint64_t>::nil();
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<expr>::Cons>(l.v());
              return a00.literals().app(_self_aux(_self_aux, *a10));
            }
          };
          auto aux = [&](const List<expr> &l) -> List<uint64_t> {
            return aux_impl(aux_impl, l);
          };
          _result = aux(*a0);
        } else {
          const auto &[a0] = std::get<typename expr::Mul>(_sv.v());
          auto aux_impl = [](auto &_self_aux,
                             const List<expr> &l) -> List<uint64_t> {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return List<uint64_t>::nil();
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<expr>::Cons>(l.v());
              return a00.literals().app(_self_aux(_self_aux, *a10));
            }
          };
          auto aux = [&](const List<expr> &l) -> List<uint64_t> {
            return aux_impl(aux_impl, l);
          };
          _result = aux(*a0);
        }
      }
      return _result;
    }

    uint64_t expr_depth() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      using _Frame = std::variant<_Enter>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified expr_depth: _Enter.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        auto _f = std::move(std::get<_Enter>(_frame));
        const expr *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
          _result = UINT64_C(0);
        } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
          const auto &[a0] = std::get<typename expr::Add>(_sv.v());
          auto aux_impl = [](auto &_self_aux, const List<expr> &l) -> uint64_t {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return UINT64_C(0);
            } else {
              const auto &[a1, a2] = std::get<typename List<expr>::Cons>(l.v());
              return std::max(a1.expr_depth(), _self_aux(_self_aux, *a2));
            }
          };
          auto aux = [&](const List<expr> &l) -> uint64_t {
            return aux_impl(aux_impl, l);
          };
          _result = (aux(*a0) + 1);
        } else {
          const auto &[a0] = std::get<typename expr::Mul>(_sv.v());
          auto aux_impl = [](auto &_self_aux, const List<expr> &l) -> uint64_t {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return UINT64_C(0);
            } else {
              const auto &[a1, a2] = std::get<typename List<expr>::Cons>(l.v());
              return std::max(a1.expr_depth(), _self_aux(_self_aux, *a2));
            }
          };
          auto aux = [&](const List<expr> &l) -> uint64_t {
            return aux_impl(aux_impl, l);
          };
          _result = (aux(*a0) + 1);
        }
      }
      return _result;
    }

    uint64_t expr_size() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      using _Frame = std::variant<_Enter>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified expr_size: _Enter.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        auto _f = std::move(std::get<_Enter>(_frame));
        const expr *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
          _result = UINT64_C(1);
        } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
          const auto &[a0] = std::get<typename expr::Add>(_sv.v());
          auto aux_impl = [](auto &_self_aux, const List<expr> &l) -> uint64_t {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return UINT64_C(0);
            } else {
              const auto &[a1, a2] = std::get<typename List<expr>::Cons>(l.v());
              return (a1.expr_size() + _self_aux(_self_aux, *a2));
            }
          };
          auto aux = [&](const List<expr> &l) -> uint64_t {
            return aux_impl(aux_impl, l);
          };
          _result = (aux(*a0) + 1);
        } else {
          const auto &[a0] = std::get<typename expr::Mul>(_sv.v());
          auto aux_impl = [](auto &_self_aux, const List<expr> &l) -> uint64_t {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return UINT64_C(0);
            } else {
              const auto &[a1, a2] = std::get<typename List<expr>::Cons>(l.v());
              return (a1.expr_size() + _self_aux(_self_aux, *a2));
            }
          };
          auto aux = [&](const List<expr> &l) -> uint64_t {
            return aux_impl(aux_impl, l);
          };
          _result = (aux(*a0) + 1);
        }
      }
      return _result;
    }

    uint64_t eval() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      using _Frame = std::variant<_Enter>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval: _Enter.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        auto _f = std::move(std::get<_Enter>(_frame));
        const expr *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
          const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
          _result = std::move(a0);
        } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
          const auto &[a0] = std::get<typename expr::Add>(_sv.v());
          auto sum_all_impl = [](auto &_self_sum_all,
                                 const List<expr> &l) -> uint64_t {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return UINT64_C(0);
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<expr>::Cons>(l.v());
              return (a00.eval() + _self_sum_all(_self_sum_all, *a10));
            }
          };
          auto sum_all = [&](const List<expr> &l) -> uint64_t {
            return sum_all_impl(sum_all_impl, l);
          };
          _result = sum_all(*a0);
        } else {
          const auto &[a0] = std::get<typename expr::Mul>(_sv.v());
          auto prod_all_impl = [](auto &_self_prod_all,
                                  const List<expr> &l) -> uint64_t {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return UINT64_C(1);
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<expr>::Cons>(l.v());
              return (a00.eval() * _self_prod_all(_self_prod_all, *a10));
            }
          };
          auto prod_all = [&](const List<expr> &l) -> uint64_t {
            return prod_all_impl(prod_all_impl, l);
          };
          _result = prod_all(*a0);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, List<expr> &> &&
               std::is_invocable_r_v<T1, F2 &, List<expr> &>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        return f0(*a0);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        return f1(*a0);
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, List<expr> &> &&
               std::is_invocable_r_v<T1, F2 &, List<expr> &>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        return f0(*a0);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        return f1(*a0);
      }
    }
  };

  static inline const expr test_add = expr::add(
      List<expr>::cons(expr::lit(UINT64_C(1)),
                       List<expr>::cons(expr::lit(UINT64_C(2)),
                                        List<expr>::cons(expr::lit(UINT64_C(3)),
                                                         List<expr>::nil()))));
  static inline const expr test_mul = expr::mul(
      List<expr>::cons(expr::lit(UINT64_C(2)),
                       List<expr>::cons(expr::lit(UINT64_C(3)),
                                        List<expr>::cons(expr::lit(UINT64_C(4)),
                                                         List<expr>::nil()))));
  static inline const expr test_nested = expr::mul(List<expr>::cons(
      expr::add(List<expr>::cons(
          expr::lit(UINT64_C(1)),
          List<expr>::cons(expr::lit(UINT64_C(2)), List<expr>::nil()))),
      List<expr>::cons(
          expr::add(List<expr>::cons(
              expr::lit(UINT64_C(3)),
              List<expr>::cons(expr::lit(UINT64_C(4)), List<expr>::nil()))),
          List<expr>::nil())));
  static inline const uint64_t test_eval_add = test_add.eval();
  static inline const uint64_t test_eval_mul = test_mul.eval();
  static inline const uint64_t test_eval_nested = test_nested.eval();
  static inline const uint64_t test_size_nested = test_nested.expr_size();
  static inline const uint64_t test_depth_nested = test_nested.expr_depth();
  static inline const List<uint64_t> test_literals = test_nested.literals();
  static inline const uint64_t test_doubled =
      test_nested.lit_map([](uint64_t n) { return (n * UINT64_C(2)); }).eval();
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<
                          std::pair<
                              std::pair<std::pair<std::pair<std::pair<uint64_t,
                                                                      uint64_t>,
                                                            uint64_t>,
                                                  uint64_t>,
                                        uint64_t>,
                              uint64_t>,
                          uint64_t>,
                      uint64_t>,
                  uint64_t>,
              uint64_t>,
          List<uint64_t>>,
      uint64_t>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(
                          std::make_pair(
                              std::make_pair(
                                  std::make_pair(
                                      std::make_pair(
                                          std::make_pair(
                                              std::make_pair(test_root_leaf,
                                                             test_root_small),
                                              test_children_leaf),
                                          test_children_small),
                                      test_children_bigger),
                                  test_eval_add),
                              test_eval_mul),
                          test_eval_nested),
                      test_size_nested),
                  test_depth_nested),
              test_literals),
          test_doubled);
};

#endif // INCLUDED_NESTED_IND
