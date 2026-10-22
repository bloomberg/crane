#ifndef INCLUDED_LOOPIFY_MUTUAL_TMC_TEMPORARY
#define INCLUDED_LOOPIFY_MUTUAL_TMC_TEMPORARY

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

/// Tail modulo cons through a partner's body.
///
/// eb's tail call to ea continues in ea's body, where ea calls eb
/// under the constructor Su: eb is lowered tail modulo cons.  Normalize
/// binds that call to a temporary, which Loopify puts back before reading
/// the constructor around it, knowing a temporary by its name.  Inlining
/// ea renamed every local of its body, the temporary too, so it was not
/// put back, the transform found no constructor around the call and left it
/// a call, and under CRANE_CHECK_IR the plan's chains were contradicted.
/// db meets the same through da's match on an enum.
struct LoopifyMutualTmcTemporary {
  struct num {
    // TYPES
    struct Z {};

    struct Su {
      std::shared_ptr<num> n;
    };

    using variant_t = std::variant<Z, Su>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    num() {}

    explicit num(Z _v) : v_(_v) {}

    explicit num(Su _v) : v_(std::move(_v)) {}

    static num z() { return num(Z{}); }

    static num su(num n) {
      return num(Su{std::make_shared<num>(std::move(n))});
    }

    // MANIPULATORS
    ~num() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<num> {
        if (auto *_alt = std::get_if<Su>(&_v)) {
          if (_alt->n && _alt->n.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->n);
          }
        }
        return nullptr;
      };
      std::shared_ptr<num> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    num(const num &) = default;
    num &operator=(const num &) = default;
    num(num &&) = default;
    num &operator=(num &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 num_rect(T1 f, F1 &&f0,
                     const num &n) { /// CraneEnter: captures varying parameters
                                     /// for each recursive call.

    struct CraneEnter {
      const num *n;
    };

    /// CraneCont_Su: saves [n1], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Su {
      std::shared_ptr<num> n1;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Su>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&n});
    /// Loopified num_rect: CraneEnter -> CraneCont_Su.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const num &n = *_f.n;
        if (std::holds_alternative<typename num::Z>(n.v())) {
          _result = f;
        } else {
          const auto &[n1] = std::get<typename num::Su>(n.v());
          _stack.emplace_back(CraneCont_Su{n1});
          _stack.emplace_back(CraneEnter{crane_raw(n1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Su>(_frame));
        std::shared_ptr<num> n1 = std::move(_f.n1);
        _result = f0(*n1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 num_rec(T1 f, F1 &&f0, const num &n) {
    return num_rect<T1>(std::move(f), f0, n);
  }
  enum class Color { RED, GREEN, BLUE };

  template <typename T1> static T1 color_rect(T1 f, T1 f0, T1 f1, Color c) {
    switch (c) {
    case Color::RED: {
      return f;
    }
    case Color::GREEN: {
      return f0;
    }
    case Color::BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 color_rec(T1 f, T1 f0, T1 f1, Color c) {
    return color_rect<T1>(std::move(f), std::move(f0), std::move(f1), c);
  }

  static num ea(const num &n);
  static num eb(const num &n, num x);
  static num da(Color c, const num &n);
  static num db(const num &n);
  static num of_nat(uint64_t n);
  static uint64_t to_nat(const num &n);
  static uint64_t run_ea(uint64_t n);
  static uint64_t run_eb(uint64_t n, uint64_t x);
  static uint64_t run_da(Color c, uint64_t n);
  static uint64_t run_db(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_MUTUAL_TMC_TEMPORARY
