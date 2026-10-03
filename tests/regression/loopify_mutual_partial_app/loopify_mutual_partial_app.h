#ifndef INCLUDED_LOOPIFY_MUTUAL_PARTIAL_APP
#define INCLUDED_LOOPIFY_MUTUAL_PARTIAL_APP

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <any>
#include <atomic>
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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
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
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> *_write = &_head;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<T1>>(List<T1>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<T1>>(typename List<T1>::Cons(f(a0), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};

/// A polymorphic mutual traversal in the shape of Vellvm's
/// Traversal.ft_exp / ft_metadata: a class parameter (Endo), a function
/// parameter f, a local closure over the recursion (ftpair), and the
/// mutual partner partially applied under map (map (ft_md U V f) l).
/// With Set Crane Loopify the generated loop binds a non-const lvalue
/// reference to a moved temporary ("non-const lvalue reference to type
/// '(lambda ...)' cannot bind to a temporary") and calls ft_e with
/// arguments it has no overload for.
///
/// loopify_mutual_result_types (fixed in a9df8ed7e) is the same pair
/// without the parameters; this is what is left of Vellvm's global
/// Set Crane Loopify on 19ffa36ec: all 4 of its remaining errors.
struct LoopifyMutualPartialApp {
  template <typename t> using Endo = crane::fn<t(t)>;

  template <typename T1>
  static T1 endo(std::type_identity_t<Endo<T1>> endo0, T1 x0_) {
    return endo0(std::move(x0_));
  }
  template <typename U> struct e;
  template <typename U> struct md;

  template <typename U> struct e {
    // TYPES
    struct Leaf {
      uint64_t n;
    };

    struct Tag {
      U u;
    };

    struct Add {
      std::shared_ptr<e<U>> a;
      std::shared_ptr<e<U>> b;
    };

    struct Meta {
      std::shared_ptr<md<U>> m;
    };

    using variant_t = std::variant<Leaf, Tag, Add, Meta>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    e() {}

    explicit e(Leaf _v) : v_(std::move(_v)) {}

    explicit e(Tag _v) : v_(std::move(_v)) {}

    explicit e(Add _v) : v_(std::move(_v)) {}

    explicit e(Meta _v) : v_(std::move(_v)) {}

    template <typename _U>
    e(const e<_U> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename e<_U>::Leaf>(_other.v())) {
              const auto &[n] = std::get<typename e<_U>::Leaf>(_other.v());
              return Leaf{n};
            } else {
              if (std::holds_alternative<typename e<_U>::Tag>(_other.v())) {
                const auto &[u] = std::get<typename e<_U>::Tag>(_other.v());
                return Tag{[&]() -> U {
                  if constexpr (crane_convertible<U, const _U &>) {
                    return crane_convert<U>(u);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }()};
              } else {
                if (std::holds_alternative<typename e<_U>::Add>(_other.v())) {
                  const auto &[a, b] =
                      std::get<typename e<_U>::Add>(_other.v());
                  return Add{
                      (a ? std::make_shared<e<U>>(crane_convert<e<U>>(*a))
                         : nullptr),
                      (b ? std::make_shared<e<U>>(crane_convert<e<U>>(*b))
                         : nullptr)};
                } else {
                  const auto &[m] = std::get<typename e<_U>::Meta>(_other.v());
                  return Meta{
                      (m ? std::make_shared<md<U>>(crane_convert<md<U>>(*m))
                         : nullptr)};
                }
              }
            }
          }()) {}

    static e<U> leaf(uint64_t n) { return e<U>(Leaf{n}); }

    static e<U> tag(U u) { return e<U>(Tag{std::move(u)}); }

    static e<U> add(e<U> a, e<U> b) {
      return e<U>(Add{std::make_shared<e<U>>(std::move(a)),
                      std::make_shared<e<U>>(std::move(b))});
    }

    static e<U> meta(md<U> m) {
      return e<U>(Meta{std::make_shared<md<U>>(std::move(m))});
    }

    // MANIPULATORS
    ~e() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Add>(&_v)) {
          if (_alt->a && _alt->a.use_count() == 1) {
            _stack.push_back(std::move(_alt->a));
          }
          if (_alt->b && _alt->b.use_count() == 1) {
            _stack.push_back(std::move(_alt->b));
          }
        }
        if (auto *_alt = std::get_if<Meta>(&_v)) {
          if (_alt->m && _alt->m.use_count() == 1) {
            _stack.push_back(std::move(_alt->m));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<e<U>>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<md<U>>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename md<U>::MConst>(&_pv)) {
                if (_alt->x && _alt->x.use_count() == 1) {
                  _stack.push_back(std::move(_alt->x));
                }
              }
              if (auto *_alt = std::get_if<typename md<U>::MPair>(&_pv)) {
                if (_alt->a && _alt->a.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a));
                }
                if (_alt->b && _alt->b.use_count() == 1) {
                  _stack.push_back(std::move(_alt->b));
                }
              }
            }
          }
        }
      }
    }

    e(const e &) = default;
    e &operator=(const e &) = default;
    e(e &&) noexcept = default;
    e &operator=(e &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename U> struct md {
    // TYPES
    struct MNull {};

    struct MConst {
      U u;
      std::shared_ptr<e<U>> x;
    };

    struct MNode {
      std::shared_ptr<List<md<U>>> l;
    };

    struct MPair {
      std::shared_ptr<md<U>> a;
      std::shared_ptr<md<U>> b;
    };

    using variant_t = std::variant<MNull, MConst, MNode, MPair>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    md() {}

    explicit md(MNull _v) : v_(_v) {}

    explicit md(MConst _v) : v_(std::move(_v)) {}

    explicit md(MNode _v) : v_(std::move(_v)) {}

    explicit md(MPair _v) : v_(std::move(_v)) {}

    template <typename _U>
    md(const md<_U> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename md<_U>::MNull>(_other.v())) {
              return MNull{};
            } else {
              if (std::holds_alternative<typename md<_U>::MConst>(_other.v())) {
                const auto &[u, x] =
                    std::get<typename md<_U>::MConst>(_other.v());
                return MConst{
                    [&]() -> U {
                      if constexpr (crane_convertible<U, const _U &>) {
                        return crane_convert<U>(u);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    (x ? std::make_shared<e<U>>(crane_convert<e<U>>(*x))
                       : nullptr)};
              } else {
                if (std::holds_alternative<typename md<_U>::MNode>(
                        _other.v())) {
                  const auto &[l] =
                      std::get<typename md<_U>::MNode>(_other.v());
                  return MNode{(l ? std::make_shared<List<md<U>>>(
                                        crane_convert<List<md<U>>>(*l))
                                  : nullptr)};
                } else {
                  const auto &[a, b] =
                      std::get<typename md<_U>::MPair>(_other.v());
                  return MPair{
                      (a ? std::make_shared<md<U>>(crane_convert<md<U>>(*a))
                         : nullptr),
                      (b ? std::make_shared<md<U>>(crane_convert<md<U>>(*b))
                         : nullptr)};
                }
              }
            }
          }()) {}

    static md<U> mnull() { return md<U>(MNull{}); }

    static md<U> mconst(U u, e<U> x) {
      return md<U>(MConst{std::move(u), std::make_shared<e<U>>(std::move(x))});
    }

    static md<U> mnode(List<md<U>> l) {
      return md<U>(MNode{std::make_shared<List<md<U>>>(std::move(l))});
    }

    static md<U> mpair(md<U> a, md<U> b) {
      return md<U>(MPair{std::make_shared<md<U>>(std::move(a)),
                         std::make_shared<md<U>>(std::move(b))});
    }

    // MANIPULATORS
    ~md() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<MConst>(&_v)) {
          if (_alt->x && _alt->x.use_count() == 1) {
            _stack.push_back(std::move(_alt->x));
          }
        }
        if (auto *_alt = std::get_if<MNode>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto _lp = _alt->l.get();
            while (
                std::holds_alternative<typename List<md<U>>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<md<U>>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<md<U>>(std::move(_lc.a)));
              if (_lc.l && _lc.l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->l.reset();
          }
        }
        if (auto *_alt = std::get_if<MPair>(&_v)) {
          if (_alt->a && _alt->a.use_count() == 1) {
            _stack.push_back(std::move(_alt->a));
          }
          if (_alt->b && _alt->b.use_count() == 1) {
            _stack.push_back(std::move(_alt->b));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<md<U>>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<e<U>>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename e<U>::Add>(&_pv)) {
                if (_alt->a && _alt->a.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a));
                }
                if (_alt->b && _alt->b.use_count() == 1) {
                  _stack.push_back(std::move(_alt->b));
                }
              }
              if (auto *_alt = std::get_if<typename e<U>::Meta>(&_pv)) {
                if (_alt->m && _alt->m.use_count() == 1) {
                  _stack.push_back(std::move(_alt->m));
                }
              }
            }
          }
        }
      }
    }

    md(const md &) = default;
    md &operator=(const md &) = default;
    md(md &&) noexcept = default;
    md &operator=(md &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0, typename F1, typename F2,
            typename F3>
    requires std::is_invocable_r_v<T2, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T2, F1 &, T1 &> &&
             std::is_invocable_r_v<T2, F2 &, e<T1> &, T2 &, e<T1> &, T2 &> &&
             std::is_invocable_r_v<T2, F3 &, md<T1> &>
  static T2 e_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2,
                   const e<T1> &e0) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      const e<T1> *e0;
    };

    /// _Cont_Add: saves [a0, b0], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Add {
      std::shared_ptr<e<T1>> a0;
      const e<T1> *b0;
    };

    /// _Cont_Add_1: saves [_tmp2, a0, b0], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Add_1 {
      T2 _tmp2;
      std::shared_ptr<e<T1>> a0;
      const e<T1> *b0;
    };

    using _Frame = std::variant<_Enter, _Cont_Add, _Cont_Add_1>;
    T2 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&e0});
    /// Loopified e_rect: _Enter -> _Cont_Add -> _Cont_Add_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const e<T1> &e0 = *_f.e0;
        if (std::holds_alternative<typename e<T1>::Leaf>(e0.v())) {
          const auto &[n0] = std::get<typename e<T1>::Leaf>(e0.v());
          _result = f(n0);
        } else if (std::holds_alternative<typename e<T1>::Tag>(e0.v())) {
          const auto &[u0] = std::get<typename e<T1>::Tag>(e0.v());
          _result = f0(u0);
        } else if (std::holds_alternative<typename e<T1>::Add>(e0.v())) {
          const auto &[a0, b0] = std::get<typename e<T1>::Add>(e0.v());
          _stack.emplace_back(_Cont_Add{a0, crane_raw(b0)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        } else {
          const auto &[m0] = std::get<typename e<T1>::Meta>(e0.v());
          _result = f2(*m0);
        }
      } else if (std::holds_alternative<_Cont_Add>(_frame)) {
        auto _f = std::move(std::get<_Cont_Add>(_frame));
        std::shared_ptr<e<T1>> a0 = std::move(_f.a0);
        const e<T1> &b0 = *_f.b0;
        _stack.emplace_back(
            _Cont_Add_1{std::move(_result), std::move(a0), &b0});
        _stack.emplace_back(_Enter{&b0});
      } else {
        auto _f = std::move(std::get<_Cont_Add_1>(_frame));
        std::shared_ptr<e<T1>> a0 = std::move(_f.a0);
        const e<T1> &b0 = *_f.b0;
        _result = f1(*a0, std::move(_f._tmp2), b0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F0, typename F1, typename F2,
            typename F3>
    requires std::is_invocable_r_v<T2, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T2, F1 &, T1 &> &&
             std::is_invocable_r_v<T2, F2 &, e<T1> &, T2 &, e<T1> &, T2 &> &&
             std::is_invocable_r_v<T2, F3 &, md<T1> &>
  static T2 e_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2,
                  const e<T1> &e0) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      const e<T1> *e0;
    };

    /// _Cont_Add: saves [a0, b0], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Add {
      std::shared_ptr<e<T1>> a0;
      const e<T1> *b0;
    };

    /// _Cont_Add_1: saves [_tmp2, a0, b0], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Add_1 {
      T2 _tmp2;
      std::shared_ptr<e<T1>> a0;
      const e<T1> *b0;
    };

    using _Frame = std::variant<_Enter, _Cont_Add, _Cont_Add_1>;
    T2 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&e0});
    /// Loopified e_rec: _Enter -> _Cont_Add -> _Cont_Add_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const e<T1> &e0 = *_f.e0;
        if (std::holds_alternative<typename e<T1>::Leaf>(e0.v())) {
          const auto &[n0] = std::get<typename e<T1>::Leaf>(e0.v());
          _result = f(n0);
        } else if (std::holds_alternative<typename e<T1>::Tag>(e0.v())) {
          const auto &[u0] = std::get<typename e<T1>::Tag>(e0.v());
          _result = f0(u0);
        } else if (std::holds_alternative<typename e<T1>::Add>(e0.v())) {
          const auto &[a0, b0] = std::get<typename e<T1>::Add>(e0.v());
          _stack.emplace_back(_Cont_Add{a0, crane_raw(b0)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        } else {
          const auto &[m0] = std::get<typename e<T1>::Meta>(e0.v());
          _result = f2(*m0);
        }
      } else if (std::holds_alternative<_Cont_Add>(_frame)) {
        auto _f = std::move(std::get<_Cont_Add>(_frame));
        std::shared_ptr<e<T1>> a0 = std::move(_f.a0);
        const e<T1> &b0 = *_f.b0;
        _stack.emplace_back(
            _Cont_Add_1{std::move(_result), std::move(a0), &b0});
        _stack.emplace_back(_Enter{&b0});
      } else {
        auto _f = std::move(std::get<_Cont_Add_1>(_frame));
        std::shared_ptr<e<T1>> a0 = std::move(_f.a0);
        const e<T1> &b0 = *_f.b0;
        _result = f1(*a0, std::move(_f._tmp2), b0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1, typename F2, typename F3>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, e<T1> &> &&
             std::is_invocable_r_v<T2, F2 &, List<md<T1>> &> &&
             std::is_invocable_r_v<T2, F3 &, md<T1> &, T2 &, md<T1> &, T2 &>
  static T2 md_rect(T2 f, F1 &&f0, F2 &&f1, F3 &&f2,
                    const md<T1> &m) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const md<T1> *m;
    };

    /// _Cont_MPair: saves [a0, b0], resumes after recursive call, then
    /// processes rest.
    struct _Cont_MPair {
      std::shared_ptr<md<T1>> a0;
      const md<T1> *b0;
    };

    /// _Cont_MPair_1: saves [_tmp2, a0, b0], resumes after recursive call, then
    /// processes rest.
    struct _Cont_MPair_1 {
      T2 _tmp2;
      std::shared_ptr<md<T1>> a0;
      const md<T1> *b0;
    };

    using _Frame = std::variant<_Enter, _Cont_MPair, _Cont_MPair_1>;
    T2 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&m});
    /// Loopified md_rect: _Enter -> _Cont_MPair -> _Cont_MPair_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const md<T1> &m = *_f.m;
        if (std::holds_alternative<typename md<T1>::MNull>(m.v())) {
          _result = f;
        } else if (std::holds_alternative<typename md<T1>::MConst>(m.v())) {
          const auto &[u0, x0] = std::get<typename md<T1>::MConst>(m.v());
          _result = f0(u0, *x0);
        } else if (std::holds_alternative<typename md<T1>::MNode>(m.v())) {
          const auto &[l0] = std::get<typename md<T1>::MNode>(m.v());
          _result = f1(*l0);
        } else {
          const auto &[a0, b0] = std::get<typename md<T1>::MPair>(m.v());
          _stack.emplace_back(_Cont_MPair{a0, crane_raw(b0)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_Cont_MPair>(_frame)) {
        auto _f = std::move(std::get<_Cont_MPair>(_frame));
        std::shared_ptr<md<T1>> a0 = std::move(_f.a0);
        const md<T1> &b0 = *_f.b0;
        _stack.emplace_back(
            _Cont_MPair_1{std::move(_result), std::move(a0), &b0});
        _stack.emplace_back(_Enter{&b0});
      } else {
        auto _f = std::move(std::get<_Cont_MPair_1>(_frame));
        std::shared_ptr<md<T1>> a0 = std::move(_f.a0);
        const md<T1> &b0 = *_f.b0;
        _result = f2(*a0, std::move(_f._tmp2), b0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1, typename F2, typename F3>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, e<T1> &> &&
             std::is_invocable_r_v<T2, F2 &, List<md<T1>> &> &&
             std::is_invocable_r_v<T2, F3 &, md<T1> &, T2 &, md<T1> &, T2 &>
  static T2 md_rec(T2 f, F1 &&f0, F2 &&f1, F3 &&f2,
                   const md<T1> &m) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      const md<T1> *m;
    };

    /// _Cont_MPair: saves [a0, b0], resumes after recursive call, then
    /// processes rest.
    struct _Cont_MPair {
      std::shared_ptr<md<T1>> a0;
      const md<T1> *b0;
    };

    /// _Cont_MPair_1: saves [_tmp2, a0, b0], resumes after recursive call, then
    /// processes rest.
    struct _Cont_MPair_1 {
      T2 _tmp2;
      std::shared_ptr<md<T1>> a0;
      const md<T1> *b0;
    };

    using _Frame = std::variant<_Enter, _Cont_MPair, _Cont_MPair_1>;
    T2 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&m});
    /// Loopified md_rec: _Enter -> _Cont_MPair -> _Cont_MPair_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const md<T1> &m = *_f.m;
        if (std::holds_alternative<typename md<T1>::MNull>(m.v())) {
          _result = f;
        } else if (std::holds_alternative<typename md<T1>::MConst>(m.v())) {
          const auto &[u0, x0] = std::get<typename md<T1>::MConst>(m.v());
          _result = f0(u0, *x0);
        } else if (std::holds_alternative<typename md<T1>::MNode>(m.v())) {
          const auto &[l0] = std::get<typename md<T1>::MNode>(m.v());
          _result = f1(*l0);
        } else {
          const auto &[a0, b0] = std::get<typename md<T1>::MPair>(m.v());
          _stack.emplace_back(_Cont_MPair{a0, crane_raw(b0)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_Cont_MPair>(_frame)) {
        auto _f = std::move(std::get<_Cont_MPair>(_frame));
        std::shared_ptr<md<T1>> a0 = std::move(_f.a0);
        const md<T1> &b0 = *_f.b0;
        _stack.emplace_back(
            _Cont_MPair_1{std::move(_result), std::move(a0), &b0});
        _stack.emplace_back(_Enter{&b0});
      } else {
        auto _f = std::move(std::get<_Cont_MPair_1>(_frame));
        std::shared_ptr<md<T1>> a0 = std::move(_f.a0);
        const md<T1> &b0 = *_f.b0;
        _result = f2(*a0, std::move(_f._tmp2), b0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &>
  static e<T2> ft_e(Endo<uint64_t> h, F1 &&f,
                    const e<T1> &x) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      e<T1> x;
      std::decay_t<F1> f;
      Endo<uint64_t> h;
    };

    /// _Cont_Add: saves [b0, f, h], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Add {
      std::shared_ptr<e<T1>> b0;
      std::decay_t<F1> f;
      Endo<uint64_t> h;
    };

    /// _Cont_Add_1: saves [_tmp2], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Add_1 {
      e<T2> _tmp2;
    };

    using _Frame = std::variant<_Enter, _Cont_Add, _Cont_Add_1>;
    e<T2> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{x, std::move(f), std::move(h)});
    /// Loopified ft_e: _Enter -> _Cont_Add -> _Cont_Add_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const e<T1> &x = std::move(_f.x);
        auto f = std::move(_f.f);
        Endo<uint64_t> h = std::move(_f.h);
        if (std::holds_alternative<typename e<T1>::Leaf>(x.v())) {
          const auto &[n0] = std::get<typename e<T1>::Leaf>(x.v());
          _result = e<T2>::leaf(endo<uint64_t>(std::move(h), n0));
        } else if (std::holds_alternative<typename e<T1>::Tag>(x.v())) {
          const auto &[u0] = std::get<typename e<T1>::Tag>(x.v());
          _result = e<T2>::tag(f(u0));
        } else if (std::holds_alternative<typename e<T1>::Add>(x.v())) {
          const auto &[a0, b0] = std::get<typename e<T1>::Add>(x.v());
          _stack.emplace_back(_Cont_Add{b0, f, h});
          _stack.emplace_back(_Enter{*a0, std::move(f), std::move(h)});
        } else {
          const auto &[m0] = std::get<typename e<T1>::Meta>(x.v());
          _result = e<T2>::meta([](Endo<uint64_t> _inl_h, auto &&_inl_f,
                                   const md<T1> &_inl_m) -> md<T2> {
            if (std::holds_alternative<typename md<T1>::MNull>(_inl_m.v())) {
              return md<T2>::mnull();
            } else if (std::holds_alternative<typename md<T1>::MConst>(
                           _inl_m.v())) {
              const auto &[_inl_u0, _inl_x0] =
                  std::get<typename md<T1>::MConst>(_inl_m.v());
              e<T2> _inl__tmp1 = ft_e<T1, T2>(_inl_h, _inl_f, *_inl_x0);
              return md<T2>::mconst(_inl_f(_inl_u0), std::move(_inl__tmp1));
            } else if (std::holds_alternative<typename md<T1>::MNode>(
                           _inl_m.v())) {
              const auto &[_inl_l0] =
                  std::get<typename md<T1>::MNode>(_inl_m.v());
              const List<md<T1>> &_inl_l0_value = *_inl_l0;
              return md<T2>::mnode(
                  _inl_l0_value.template map<md<T2>>([=](md<T1> _x0) -> md<T2> {
                    return ft_md<T1, T2>(_inl_h, _inl_f, _x0);
                  }));
            } else {
              const auto &[_inl_a0, _inl_b0] =
                  std::get<typename md<T1>::MPair>(_inl_m.v());
              md<T2> _inl__tmp3 = ft_md<T1, T2>(_inl_h, _inl_f, *_inl_a0);
              md<T2> _inl__tmp2 = ft_md<T1, T2>(_inl_h, _inl_f, *_inl_b0);
              return md<T2>::mpair(std::move(_inl__tmp3),
                                   std::move(_inl__tmp2));
            }
          }(std::move(h), std::move(f), *m0));
        }
      } else if (std::holds_alternative<_Cont_Add>(_frame)) {
        auto _f = std::move(std::get<_Cont_Add>(_frame));
        std::shared_ptr<e<T1>> b0 = std::move(_f.b0);
        std::decay_t<F1> f = std::move(_f.f);
        Endo<uint64_t> h = std::move(_f.h);
        _stack.emplace_back(_Cont_Add_1{std::move(_result)});
        _stack.emplace_back(_Enter{*b0, std::move(f), std::move(h)});
      } else {
        auto _f = std::move(std::get<_Cont_Add_1>(_frame));
        _result = e<T2>::add(std::move(_f._tmp2), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &>
  static md<T2> ft_md(Endo<uint64_t> h, F1 &&f,
                      const md<T1> &m) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

    struct _Enter {
      md<T1> m;
      std::decay_t<F1> f;
      Endo<uint64_t> h;
    };

    /// _Cont_MPair: saves [b0, f, h], resumes after recursive call, then
    /// processes rest.
    struct _Cont_MPair {
      std::shared_ptr<md<T1>> b0;
      std::decay_t<F1> f;
      Endo<uint64_t> h;
    };

    /// _Cont_MPair_1: saves [_tmp3], resumes after recursive call, then
    /// processes rest.
    struct _Cont_MPair_1 {
      md<T2> _tmp3;
    };

    using _Frame = std::variant<_Enter, _Cont_MPair, _Cont_MPair_1>;
    md<T2> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{m, f, std::move(h)});
    /// Loopified ft_md: _Enter -> _Cont_MPair -> _Cont_MPair_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const md<T1> &m = std::move(_f.m);
        auto f = std::move(_f.f);
        Endo<uint64_t> h = std::move(_f.h);
        if (std::holds_alternative<typename md<T1>::MNull>(m.v())) {
          _result = md<T2>::mnull();
        } else if (std::holds_alternative<typename md<T1>::MConst>(m.v())) {
          const auto &[u0, x0] = std::get<typename md<T1>::MConst>(m.v());
          _result = md<T2>::mconst(
              f(u0),
              [](Endo<uint64_t> _inl_h, auto &&_inl_f,
                 const e<T1> &_inl_x) -> e<T2> {
                if (std::holds_alternative<typename e<T1>::Leaf>(_inl_x.v())) {
                  const auto &[_inl_n0] =
                      std::get<typename e<T1>::Leaf>(_inl_x.v());
                  return e<T2>::leaf(endo<uint64_t>(_inl_h, _inl_n0));
                } else if (std::holds_alternative<typename e<T1>::Tag>(
                               _inl_x.v())) {
                  const auto &[_inl_u0] =
                      std::get<typename e<T1>::Tag>(_inl_x.v());
                  return e<T2>::tag(_inl_f(_inl_u0));
                } else if (std::holds_alternative<typename e<T1>::Add>(
                               _inl_x.v())) {
                  const auto &[_inl_a0, _inl_b0] =
                      std::get<typename e<T1>::Add>(_inl_x.v());
                  e<T2> _inl__tmp2 = ft_e<T1, T2>(_inl_h, _inl_f, *_inl_a0);
                  e<T2> _inl__tmp1 = ft_e<T1, T2>(_inl_h, _inl_f, *_inl_b0);
                  return e<T2>::add(std::move(_inl__tmp2),
                                    std::move(_inl__tmp1));
                } else {
                  const auto &[_inl_m0] =
                      std::get<typename e<T1>::Meta>(_inl_x.v());
                  md<T2> _inl__tmp3 = ft_md<T1, T2>(_inl_h, _inl_f, *_inl_m0);
                  return e<T2>::meta(std::move(_inl__tmp3));
                }
              }(h, f, *x0));
        } else if (std::holds_alternative<typename md<T1>::MNode>(m.v())) {
          const auto &[l0] = std::get<typename md<T1>::MNode>(m.v());
          const List<md<T1>> &l0_value = *l0;
          _result = md<T2>::mnode(l0_value.template map<md<T2>>(
              [=](md<T1> _x0) -> md<T2> { return ft_md<T1, T2>(h, f, _x0); }));
        } else {
          const auto &[a0, b0] = std::get<typename md<T1>::MPair>(m.v());
          _stack.emplace_back(_Cont_MPair{b0, f, h});
          _stack.emplace_back(_Enter{*a0, f, h});
        }
      } else if (std::holds_alternative<_Cont_MPair>(_frame)) {
        auto _f = std::move(std::get<_Cont_MPair>(_frame));
        std::shared_ptr<md<T1>> b0 = std::move(_f.b0);
        std::decay_t<F1> f = std::move(_f.f);
        Endo<uint64_t> h = std::move(_f.h);
        _stack.emplace_back(_Cont_MPair_1{std::move(_result)});
        _stack.emplace_back(_Enter{*b0, std::move(f), std::move(h)});
      } else {
        auto _f = std::move(std::get<_Cont_MPair_1>(_frame));
        _result = md<T2>::mpair(std::move(_f._tmp3), std::move(_result));
      }
    }
    return _result;
  }

  static uint64_t sum_e(const e<uint64_t> &x);
  static uint64_t sum_md(const md<uint64_t> &m);
  static inline const Endo<uint64_t> endo_double = [](uint64_t n) {
    return (UINT64_C(2) * n);
  };
  static inline const e<uint64_t> sample = e<uint64_t>::add(
      e<uint64_t>::leaf(UINT64_C(1)),
      e<uint64_t>::meta(md<uint64_t>::mpair(
          md<uint64_t>::mconst(UINT64_C(5),
                               e<uint64_t>::add(e<uint64_t>::leaf(UINT64_C(2)),
                                                e<uint64_t>::tag(UINT64_C(7)))),
          md<uint64_t>::mnode(List<md<uint64_t>>::cons(
              md<uint64_t>::mnull(),
              List<md<uint64_t>>::cons(
                  md<uint64_t>::mconst(UINT64_C(1),
                                       e<uint64_t>::leaf(UINT64_C(4))),
                  List<md<uint64_t>>::nil()))))));
  /// leaves doubled: 2*(1+2+4) = 14; tags and consts +100 each: 107 + 105 + 101
  /// = 313
  static bool check(std::monostate _x);
};

#endif // INCLUDED_LOOPIFY_MUTUAL_PARTIAL_APP
