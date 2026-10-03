#ifndef INCLUDED_LOOPIFY_MUTUAL_RESULT_TYPES
#define INCLUDED_LOOPIFY_MUTUAL_RESULT_TYPES

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// dbl_e and dbl_md are mutually recursive and return different types
/// (e and md).  With Set Crane Loopify, dbl_e becomes a frame-stack
/// loop that inlines dbl_md as extra frames (_Enter_inl), but both halves
/// store into the one _result variable, declared at dbl_e's result type:
/// _result = Md::mnull(); assigns an md to an e -- "no viable
/// overloaded '='" -- and the resume frame then hands that _result to a
/// constructor expecting the other type.
///
/// Found in Vellvm with the global Set Crane Loopify:
/// Traversal.ft_exp / ft_metadata, 4 of its 59 errors.
struct LoopifyMutualResultTypes {
  struct e;
  struct md;

  struct e {
    // TYPES
    struct Leaf {
      uint64_t n;
    };

    struct Add {
      std::shared_ptr<e> a;
      std::shared_ptr<e> b;
    };

    struct Meta {
      std::shared_ptr<md> m;
    };

    using variant_t = std::variant<Leaf, Add, Meta>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    e() {}

    explicit e(Leaf _v) : v_(std::move(_v)) {}

    explicit e(Add _v) : v_(std::move(_v)) {}

    explicit e(Meta _v) : v_(std::move(_v)) {}

    static e leaf(uint64_t n) { return e(Leaf{n}); }

    static e add(e a, e b) {
      return e(Add{std::make_shared<e>(std::move(a)),
                   std::make_shared<e>(std::move(b))});
    }

    static e meta(md m) { return e(Meta{std::make_shared<md>(std::move(m))}); }

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
        if (auto *_sp = crane::any_cast<std::shared_ptr<e>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<md>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename md::MConst>(&_pv)) {
                if (_alt->x && _alt->x.use_count() == 1) {
                  _stack.push_back(std::move(_alt->x));
                }
              }
              if (auto *_alt = std::get_if<typename md::MPair>(&_pv)) {
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

  struct md {
    // TYPES
    struct MNull {};

    struct MConst {
      std::shared_ptr<e> x;
    };

    struct MPair {
      std::shared_ptr<md> a;
      std::shared_ptr<md> b;
    };

    using variant_t = std::variant<MNull, MConst, MPair>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    md() {}

    explicit md(MNull _v) : v_(_v) {}

    explicit md(MConst _v) : v_(std::move(_v)) {}

    explicit md(MPair _v) : v_(std::move(_v)) {}

    static md mnull() { return md(MNull{}); }

    static md mconst(e x) {
      return md(MConst{std::make_shared<e>(std::move(x))});
    }

    static md mpair(md a, md b) {
      return md(MPair{std::make_shared<md>(std::move(a)),
                      std::make_shared<md>(std::move(b))});
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
        if (auto *_sp = crane::any_cast<std::shared_ptr<md>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<e>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename e::Add>(&_pv)) {
                if (_alt->a && _alt->a.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a));
                }
                if (_alt->b && _alt->b.use_count() == 1) {
                  _stack.push_back(std::move(_alt->b));
                }
              }
              if (auto *_alt = std::get_if<typename e::Meta>(&_pv)) {
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

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, e &, T1 &, e &, T1 &> &&
             std::is_invocable_r_v<T1, F2 &, md &>
  static T1 e_rect(F0 &&f, F1 &&f0, F2 &&f1,
                   const e &e0) { /// _Enter: captures varying parameters for
                                  /// each recursive call.

    struct _Enter {
      const e *e0;
    };

    /// _Cont_Add: saves [a0, b0], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Add {
      std::shared_ptr<e> a0;
      const e *b0;
    };

    /// _Cont_Add_1: saves [_tmp2, a0, b0], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Add_1 {
      T1 _tmp2;
      std::shared_ptr<e> a0;
      const e *b0;
    };

    using _Frame = std::variant<_Enter, _Cont_Add, _Cont_Add_1>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&e0});
    /// Loopified e_rect: _Enter -> _Cont_Add -> _Cont_Add_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const e &e0 = *_f.e0;
        if (std::holds_alternative<typename e::Leaf>(e0.v())) {
          const auto &[n0] = std::get<typename e::Leaf>(e0.v());
          _result = f(n0);
        } else if (std::holds_alternative<typename e::Add>(e0.v())) {
          const auto &[a0, b0] = std::get<typename e::Add>(e0.v());
          _stack.emplace_back(_Cont_Add{a0, crane_raw(b0)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        } else {
          const auto &[m0] = std::get<typename e::Meta>(e0.v());
          _result = f1(*m0);
        }
      } else if (std::holds_alternative<_Cont_Add>(_frame)) {
        auto _f = std::move(std::get<_Cont_Add>(_frame));
        std::shared_ptr<e> a0 = std::move(_f.a0);
        const e &b0 = *_f.b0;
        _stack.emplace_back(
            _Cont_Add_1{std::move(_result), std::move(a0), &b0});
        _stack.emplace_back(_Enter{&b0});
      } else {
        auto _f = std::move(std::get<_Cont_Add_1>(_frame));
        std::shared_ptr<e> a0 = std::move(_f.a0);
        const e &b0 = *_f.b0;
        _result = f0(*a0, std::move(_f._tmp2), b0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, e &, T1 &, e &, T1 &> &&
             std::is_invocable_r_v<T1, F2 &, md &>
  static T1 e_rec(F0 &&f, F1 &&f0, F2 &&f1,
                  const e &e0) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const e *e0;
    };

    /// _Cont_Add: saves [a0, b0], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Add {
      std::shared_ptr<e> a0;
      const e *b0;
    };

    /// _Cont_Add_1: saves [_tmp2, a0, b0], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Add_1 {
      T1 _tmp2;
      std::shared_ptr<e> a0;
      const e *b0;
    };

    using _Frame = std::variant<_Enter, _Cont_Add, _Cont_Add_1>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&e0});
    /// Loopified e_rec: _Enter -> _Cont_Add -> _Cont_Add_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const e &e0 = *_f.e0;
        if (std::holds_alternative<typename e::Leaf>(e0.v())) {
          const auto &[n0] = std::get<typename e::Leaf>(e0.v());
          _result = f(n0);
        } else if (std::holds_alternative<typename e::Add>(e0.v())) {
          const auto &[a0, b0] = std::get<typename e::Add>(e0.v());
          _stack.emplace_back(_Cont_Add{a0, crane_raw(b0)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        } else {
          const auto &[m0] = std::get<typename e::Meta>(e0.v());
          _result = f1(*m0);
        }
      } else if (std::holds_alternative<_Cont_Add>(_frame)) {
        auto _f = std::move(std::get<_Cont_Add>(_frame));
        std::shared_ptr<e> a0 = std::move(_f.a0);
        const e &b0 = *_f.b0;
        _stack.emplace_back(
            _Cont_Add_1{std::move(_result), std::move(a0), &b0});
        _stack.emplace_back(_Enter{&b0});
      } else {
        auto _f = std::move(std::get<_Cont_Add_1>(_frame));
        std::shared_ptr<e> a0 = std::move(_f.a0);
        const e &b0 = *_f.b0;
        _result = f0(*a0, std::move(_f._tmp2), b0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F1 &, e &> &&
             std::is_invocable_r_v<T1, F2 &, md &, T1 &, md &, T1 &>
  static T1 md_rect(T1 f, F1 &&f0, F2 &&f1,
                    const md &m) { /// _Enter: captures varying parameters for
                                   /// each recursive call.

    struct _Enter {
      const md *m;
    };

    /// _Cont_MPair: saves [a0, b0], resumes after recursive call, then
    /// processes rest.
    struct _Cont_MPair {
      std::shared_ptr<md> a0;
      const md *b0;
    };

    /// _Cont_MPair_1: saves [_tmp2, a0, b0], resumes after recursive call, then
    /// processes rest.
    struct _Cont_MPair_1 {
      T1 _tmp2;
      std::shared_ptr<md> a0;
      const md *b0;
    };

    using _Frame = std::variant<_Enter, _Cont_MPair, _Cont_MPair_1>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&m});
    /// Loopified md_rect: _Enter -> _Cont_MPair -> _Cont_MPair_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const md &m = *_f.m;
        if (std::holds_alternative<typename md::MNull>(m.v())) {
          _result = f;
        } else if (std::holds_alternative<typename md::MConst>(m.v())) {
          const auto &[x0] = std::get<typename md::MConst>(m.v());
          _result = f0(*x0);
        } else {
          const auto &[a0, b0] = std::get<typename md::MPair>(m.v());
          _stack.emplace_back(_Cont_MPair{a0, crane_raw(b0)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_Cont_MPair>(_frame)) {
        auto _f = std::move(std::get<_Cont_MPair>(_frame));
        std::shared_ptr<md> a0 = std::move(_f.a0);
        const md &b0 = *_f.b0;
        _stack.emplace_back(
            _Cont_MPair_1{std::move(_result), std::move(a0), &b0});
        _stack.emplace_back(_Enter{&b0});
      } else {
        auto _f = std::move(std::get<_Cont_MPair_1>(_frame));
        std::shared_ptr<md> a0 = std::move(_f.a0);
        const md &b0 = *_f.b0;
        _result = f1(*a0, std::move(_f._tmp2), b0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F1 &, e &> &&
             std::is_invocable_r_v<T1, F2 &, md &, T1 &, md &, T1 &>
  static T1 md_rec(T1 f, F1 &&f0, F2 &&f1,
                   const md &m) { /// _Enter: captures varying parameters for
                                  /// each recursive call.

    struct _Enter {
      const md *m;
    };

    /// _Cont_MPair: saves [a0, b0], resumes after recursive call, then
    /// processes rest.
    struct _Cont_MPair {
      std::shared_ptr<md> a0;
      const md *b0;
    };

    /// _Cont_MPair_1: saves [_tmp2, a0, b0], resumes after recursive call, then
    /// processes rest.
    struct _Cont_MPair_1 {
      T1 _tmp2;
      std::shared_ptr<md> a0;
      const md *b0;
    };

    using _Frame = std::variant<_Enter, _Cont_MPair, _Cont_MPair_1>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&m});
    /// Loopified md_rec: _Enter -> _Cont_MPair -> _Cont_MPair_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const md &m = *_f.m;
        if (std::holds_alternative<typename md::MNull>(m.v())) {
          _result = f;
        } else if (std::holds_alternative<typename md::MConst>(m.v())) {
          const auto &[x0] = std::get<typename md::MConst>(m.v());
          _result = f0(*x0);
        } else {
          const auto &[a0, b0] = std::get<typename md::MPair>(m.v());
          _stack.emplace_back(_Cont_MPair{a0, crane_raw(b0)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_Cont_MPair>(_frame)) {
        auto _f = std::move(std::get<_Cont_MPair>(_frame));
        std::shared_ptr<md> a0 = std::move(_f.a0);
        const md &b0 = *_f.b0;
        _stack.emplace_back(
            _Cont_MPair_1{std::move(_result), std::move(a0), &b0});
        _stack.emplace_back(_Enter{&b0});
      } else {
        auto _f = std::move(std::get<_Cont_MPair_1>(_frame));
        std::shared_ptr<md> a0 = std::move(_f.a0);
        const md &b0 = *_f.b0;
        _result = f1(*a0, std::move(_f._tmp2), b0, std::move(_result));
      }
    }
    return _result;
  }

  static e dbl_e(const e &x);
  static md dbl_md(const md &m);
  static uint64_t sum_e(const e &x);
  static uint64_t sum_md(const md &m);
  static inline const e sample =
      e::add(e::leaf(UINT64_C(1)),
             e::meta(md::mpair(
                 md::mconst(e::add(e::leaf(UINT64_C(2)), e::leaf(UINT64_C(3)))),
                 md::mpair(md::mnull(), md::mconst(e::leaf(UINT64_C(4)))))));
  /// 2 * (1 + 2 + 3 + 4)
  static bool check(std::monostate _x);
};

#endif // INCLUDED_LOOPIFY_MUTUAL_RESULT_TYPES
