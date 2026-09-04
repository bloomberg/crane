#ifndef INCLUDED_CTOR_ARG_MOVE_ALIAS_REC
#define INCLUDED_CTOR_ARG_MOVE_ALIAS_REC

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Recursive variant of ctor_arg_move_alias: the same use-after-move, but
/// reached through a tail-modulo-cons Fixpoint rather than a one-shot
/// Definition, so every level of the recursion re-triggers it.
///
/// annotate rebuilds the list, interleaving a running total.  Because h
/// occurs exactly once and o is owned (it escapes through the mynil
/// branch), Crane used to emit
///
/// {
/// auto& [a0, a1] = std::get<Mycons>(o.v_mut());
/// return mylist<inner>::mycons(
/// std::move(a0),
/// mylist<inner>::mycons(inner::icons(osum(o), inner::inil()),
/// annotate( *a1 )));
/// }
///
/// std::move(a0) hollowed out o's head element while the sibling argument
/// computed osum(o) over that same o.  The two are unsequenced; clang
/// performed the move first, so osum walked a moved-from inner whose tail
/// shared_ptr was null.
///
/// The field move is now suppressed because the branch body still reads o,
/// so run 1 = 8.
struct CtorArgMoveAliasRec {
  struct inner {
    // TYPES
    struct INil {};

    struct ICons {
      uint64_t a0;
      std::shared_ptr<inner> a1;
    };

    using variant_t = std::variant<INil, ICons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    inner() {}

    explicit inner(INil _v) : v_(_v) {}

    explicit inner(ICons _v) : v_(std::move(_v)) {}

    static inner inil() { return inner(INil{}); }

    static inner icons(uint64_t a0, inner a1) {
      return inner(ICons{a0, std::make_shared<inner>(std::move(a1))});
    }

    // MANIPULATORS
    ~inner() {
      crane::small_vector<std::shared_ptr<inner>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<ICons>(&_v)) {
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

    inner(const inner &) = default;
    inner &operator=(const inner &) = default;
    inner(inner &&) noexcept = default;
    inner &operator=(inner &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t isum() const {
      const inner *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const inner *_self;
      };

      /// _Resume_ICons: saves [a0], resumes after recursive call with _result.
      struct _Resume_ICons {
        uint64_t a0;
      };

      using _Frame = std::variant<_Enter, _Resume_ICons>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified isum: _Enter -> _Resume_ICons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const inner *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename inner::INil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] = std::get<typename inner::ICons>(_sv.v());
            _stack.emplace_back(_Resume_ICons{a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_ICons>(_frame));
          _result = (_f.a0 + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, inner &, T1 &>
    T1 inner_rec(T1 f, F1 &&f0) const {
      const inner *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const inner *_self;
      };

      /// _Resume_ICons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_ICons {
        inner a1;
        uint64_t a0;
      };

      using _Frame = std::variant<_Enter, _Resume_ICons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified inner_rec: _Enter -> _Resume_ICons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const inner *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename inner::INil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename inner::ICons>(_sv.v());
            _stack.emplace_back(_Resume_ICons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_ICons>(_frame));
          _result = f0(_f.a0, std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, inner &, T1 &>
    T1 inner_rect(T1 f, F1 &&f0) const {
      const inner *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const inner *_self;
      };

      /// _Resume_ICons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_ICons {
        inner a1;
        uint64_t a0;
      };

      using _Frame = std::variant<_Enter, _Resume_ICons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified inner_rect: _Enter -> _Resume_ICons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const inner *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename inner::INil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename inner::ICons>(_sv.v());
            _stack.emplace_back(_Resume_ICons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_ICons>(_frame));
          _result = f0(_f.a0, std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }
  };

  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::shared_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    template <typename _U> mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ = Mycons{[&]() -> A {
                            if constexpr (std::is_same_v<_U, std::any>) {
                              return crane_any_cast<A>(a0);
                            } else {
                              return A(a0);
                            }
                          }(),
                          (a1 ? std::make_shared<mylist<A>>(*a1) : nullptr)};
      }
    }

    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist<A>(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      crane::small_vector<std::shared_ptr<mylist<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
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

    mylist(const mylist &) = default;
    mylist &operator=(const mylist &) = default;
    mylist(mylist &&) noexcept = default;
    mylist &operator=(mylist &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      const mylist<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist<A> *_self;
      };

      /// _Resume_Mycons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        mylist<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rec: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist<A> *_self;
      };

      /// _Resume_Mycons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        mylist<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rect: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }
  };

  static uint64_t osum(const mylist<inner> &o);
  /// The head element h is consumed into the freshly built cell while the
  /// sibling argument still reads o.
  static mylist<inner> annotate(mylist<inner> o);
  /// For n = 1 the input is [ICons 1 INil; ICons 2 INil], so
  /// annotate yields [I 1; I 3; I 2; I 2] and run 1 = 1+3+2+2 = 8.
  static uint64_t run(uint64_t n);
};

#endif // INCLUDED_CTOR_ARG_MOVE_ALIAS_REC
