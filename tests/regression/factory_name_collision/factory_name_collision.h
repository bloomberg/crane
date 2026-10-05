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

  template <typename T1> static T1 other_rec(const T1 &f, Other _x) {
    return other_rect<T1>(f, _x);
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

    static lst cons(uint64_t a0, lst a1) {
      return lst(Cons{a0, std::make_shared<lst>(std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
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
        const auto &[a0, a1] = std::get<typename lst::Cons>(this->v());
        return a0;
      }
    }

    template <typename T1, typename F1> T1 lst_rec(const T1 &f, F1 &&f0) const {
      return this->template lst_rect<T1>(f, f0);
    }

    template <typename T1, typename F1> T1 lst_rect(T1 f, F1 &&f0) const {
      const lst *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const lst *_self;
      };

      /// CraneCont_Cons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cons {
        uint64_t a0;
        std::shared_ptr<lst> a1;
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
          const lst *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename lst::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename lst::Cons>(_sv.v());
            _stack.emplace_back(CraneCont_Cons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Cons>(_frame));
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

  static constexpr uint64_t head = UINT64_C(7);
  static constexpr uint64_t cased_sum = UINT64_C(3);
};

#endif // INCLUDED_FACTORY_NAME_COLLISION
