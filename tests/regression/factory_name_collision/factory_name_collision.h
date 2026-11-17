#ifndef INCLUDED_FACTORY_NAME_COLLISION
#define INCLUDED_FACTORY_NAME_COLLISION

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct FactoryNameCollision {
  enum class Other { ONLY };

  template <typename T1> static T1 other_rect(T1 f, Other) { return f; }

  template <typename T1> static T1 other_rec(T1 f, Other _x) {
    return other_rect<T1>(std::move(f), _x);
  }

  struct lst {
    // TYPES
    /// Methodified onto lst: its C++ name must stay clear of Nil's factory.
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

    /// Methodified onto lst: its C++ name must stay clear of Nil's factory.
    static lst nil() { return lst(Nil{}); }

    static lst cons(uint64_t a0, crane::shared_child_slot<lst> a1) {
      return lst(Cons{a0, a1.take()});
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

    uint64_t nil0() const {
      if (std::holds_alternative<typename lst::Nil>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, _] = std::get<typename lst::Cons>(this->v());
        return a0;
      }
    }

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
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
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
          _stack.pop_back();
          uint64_t a0 = _f.a0;
          std::shared_ptr<lst> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct cased {
    // TYPES
    struct Mk {
      uint64_t a0;
    };

    struct MK0 {
      uint64_t a0;
    };

    using variant_t = std::variant<Mk, MK0>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    cased() {}

    explicit cased(Mk _v) : v_(std::move(_v)) {}

    explicit cased(MK0 _v) : v_(std::move(_v)) {}

    static cased mk(uint64_t a0) { return cased(Mk{a0}); }

    static cased mk0(uint64_t a0) { return cased(MK0{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t uncase() const {
      if (std::holds_alternative<typename cased::Mk>(this->v())) {
        const auto &[a0] = std::get<typename cased::Mk>(this->v());
        return a0;
      } else {
        const auto &[a0] = std::get<typename cased::MK0>(this->v());
        return (a0 + UINT64_C(1));
      }
    }

    template <typename T1, typename F0, typename F1>
    T1 cased_rec(F0 &&f, F1 &&f0) const {
      return this->template cased_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, const uint64_t &>
    T1 cased_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename cased::Mk>(this->v())) {
        const auto &[a0] = std::get<typename cased::Mk>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename cased::MK0>(this->v());
        return f0(a0);
      }
    }
  };

  static inline const uint64_t head = lst::cons(UINT64_C(7), lst::nil()).nil0();
  static inline const uint64_t cased_sum =
      (cased::mk(UINT64_C(1)).uncase() + cased::mk0(UINT64_C(1)).uncase());
};

#endif // INCLUDED_FACTORY_NAME_COLLISION
