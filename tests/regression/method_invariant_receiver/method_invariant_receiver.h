#ifndef INCLUDED_METHOD_INVARIANT_RECEIVER
#define INCLUDED_METHOD_INVARIANT_RECEIVER

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

struct MethodInvariantReceiver {
  /// A second inductive in the module is what makes wlast methodifiable.
  struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      uint64_t a0;
      std::shared_ptr<lst> a1;
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

    static lst nil() { return lst(Nil{}); }

    static lst cons(uint64_t a0, lst a1) {
      return lst(Cons{a0, std::make_shared<lst>(std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<lst> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<lst> _cur = _next(v_mut());
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
      return this->template lst_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 lst_rect(T1 f, F1 &&f0) const {
      const lst *_self = this;

      // Explicit stack replaces the non-tail recursion of lst_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const lst *_self;
      };

      struct _after_lst_rect_in_Cons {
        uint64_t a0;
        std::shared_ptr<lst> a1;
      };

      using _frame = std::variant<_call, _after_lst_rect_in_Cons>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame _popped = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          const lst *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename lst::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename lst::Cons>(_sv.v());
            _stack.emplace_back(_after_lst_rect_in_Cons{a0, a1});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_after_lst_rect_in_Cons>(_popped));
          uint64_t a0 = _f.a0;
          std::shared_ptr<lst> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct wrap {
    // TYPES
    struct W {
      lst a0;
    };

    struct WW {
      std::shared_ptr<wrap> a0;
    };

    using variant_t = std::variant<W, WW>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    wrap() {}

    explicit wrap(W _v) : v_(std::move(_v)) {}

    explicit wrap(WW _v) : v_(std::move(_v)) {}

    static wrap w(lst a0) { return wrap(W{std::move(a0)}); }

    static wrap ww(wrap a0) {
      return wrap(WW{std::make_shared<wrap>(std::move(a0))});
    }

    // MANIPULATORS
    ~wrap() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<wrap> {
        if (auto *_alt = std::get_if<WW>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<wrap> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    wrap(const wrap &) = default;
    wrap &operator=(const wrap &) = default;
    wrap(wrap &&) = default;
    wrap &operator=(wrap &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t wdepth() const {
      const wrap *_self = this;

      // Explicit stack replaces the non-tail recursion of wdepth: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const wrap *_self;
      };

      struct _after_wdepth_in_WW {};

      using _frame = std::variant<_call, _after_wdepth_in_WW>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame _popped = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          const wrap *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename wrap::W>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0] = std::get<typename wrap::WW>(_sv.v());
            _stack.emplace_back(_after_wdepth_in_WW{});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else {
          auto _f = std::move(std::get<_after_wdepth_in_WW>(_popped));
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    }

    wrap wraps(uint64_t n) const {
      const wrap *_self = this;
      // Builds the result front to back: _write points at the empty tail the
      // next cell fills.
      std::optional<wrap> _root{};
      std::shared_ptr<wrap> *_write = nullptr;
      uint64_t _loop_n = n;
      while (true) {
        if (_loop_n <= 0) {
          auto _value = *_self;
          (_write ? *(*_write = std::make_shared<wrap>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          uint64_t k = _loop_n - 1;
          auto _cell = typename wrap::WW(nullptr);
          wrap &_node =
              (_write ? *(*_write = std::make_shared<wrap>(std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename wrap::WW>(_node.v_mut()).a0;
          _loop_n = k;
          continue;
        }
      }
      return std::move(*_root);
    }

    wrap wlast(uint64_t n) const {
      const wrap *_self = this;
      // Loop replaces the tail recursion: each recursive call updates the loop
      // variables.
      uint64_t _loop_n = n;
      while (true) {
        if (_loop_n <= 0) {
          return *_self;
        } else {
          uint64_t k = _loop_n - 1;
          _loop_n = k;
        }
      }
    }

    template <typename T1, typename F0, typename F1>
    T1 wrap_rec(F0 &&f, F1 &&f0) const {
      return this->template wrap_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const lst &>
    T1 wrap_rect(F0 &&f, F1 &&f0) const {
      const wrap *_self = this;

      // Explicit stack replaces the non-tail recursion of wrap_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const wrap *_self;
      };

      struct _after_wrap_rect_in_WW {
        std::shared_ptr<wrap> a0;
      };

      using _frame = std::variant<_call, _after_wrap_rect_in_WW>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame _popped = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          const wrap *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename wrap::W>(_sv.v())) {
            const auto &[a0] = std::get<typename wrap::W>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0] = std::get<typename wrap::WW>(_sv.v());
            _stack.emplace_back(_after_wrap_rect_in_WW{a0});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else {
          auto _f = std::move(std::get<_after_wrap_rect_in_WW>(_popped));
          std::shared_ptr<wrap> a0 = std::move(_f.a0);
          _result = f0(*a0, std::move(_result));
        }
      }
      return _result;
    }
  };

  static inline const uint64_t deep =
      wrap::w(lst::nil()).wraps(UINT64_C(3)).wlast(UINT64_C(100000)).wdepth();
};

#endif // INCLUDED_METHOD_INVARIANT_RECEIVER
