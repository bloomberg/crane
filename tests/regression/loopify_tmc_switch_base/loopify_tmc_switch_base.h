#ifndef INCLUDED_LOOPIFY_TMC_SWITCH_BASE
#define INCLUDED_LOOPIFY_TMC_SWITCH_BASE

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

/// A base case of a tail-modulo-cons loop inside an enum's match.
///
/// Tail modulo cons builds the result in a while (true) loop and leaves it
/// from a base case by break, once the base value is in place.  A match on
/// an enum is a switch, where break leaves only the switch: the loop went
/// round again on the same input and never returned.  f Blue reaches a base
/// case at once, inside the switch; f Red and f Green reach one through
/// the recursion, the second nested in a match inside the switch.
struct LoopifyTmcSwitchBase {
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
  static T1 num_rect(T1 f0, F1 &&f1,
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
          _result = f0;
        } else {
          const auto &[n1] = std::get<typename num::Su>(n.v());
          _stack.emplace_back(CraneCont_Su{n1});
          _stack.emplace_back(CraneEnter{crane_raw(n1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Su>(_frame));
        std::shared_ptr<num> n1 = std::move(_f.n1);
        _result = f1(*n1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 num_rec(T1 f0, F1 &&f1, const num &n) {
    return num_rect<T1>(std::move(f0), f1, n);
  }
  enum class Color { RED, GREEN, BLUE };

  template <typename T1> static T1 color_rect(T1 f0, T1 f1, T1 f2, Color c) {
    switch (c) {
    case Color::RED: {
      return f0;
    }
    case Color::GREEN: {
      return f1;
    }
    case Color::BLUE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 color_rec(T1 f0, T1 f1, T1 f2, Color c) {
    return color_rect<T1>(std::move(f0), std::move(f1), std::move(f2), c);
  }

  static num f(Color c, const num &n);
  static num of_nat(uint64_t n);
  static uint64_t to_nat(const num &n);
  static uint64_t run_f(Color c, uint64_t n);
};

#endif // INCLUDED_LOOPIFY_TMC_SWITCH_BASE
