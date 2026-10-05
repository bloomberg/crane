#ifndef INCLUDED_TMC_VALUE_ROOT
#define INCLUDED_TMC_VALUE_ROOT

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

struct TmcValueRoot {
  /// A list built in destination-passing style is assembled in place: its first
  /// node is the result itself, so only the cells below it are allocated, and
  /// an empty result allocates nothing.
  struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      uint64_t x;
      std::shared_ptr<lst> l;
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

    static lst cons(uint64_t x, lst l) {
      return lst(Cons{x, std::make_shared<lst>(std::move(l))});
    }

    // MANIPULATORS
    ~lst() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<lst> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->l);
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
  };

  template <typename T1, typename F1>
  static T1 lst_rect(T1 f, F1 &&f0,
                     const lst &l) { /// CraneEnter: captures varying parameters
                                     /// for each recursive call.

    struct CraneEnter {
      const lst *l;
    };

    /// CraneCont_Cons: saves [l1, x0], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Cons {
      std::shared_ptr<lst> l1;
      uint64_t x0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified lst_rect: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const lst &l = *_f.l;
        if (std::holds_alternative<typename lst::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[x0, l1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{l1, x0});
          _stack.emplace_back(CraneEnter{crane_raw(l1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        std::shared_ptr<lst> l1 = std::move(_f.l1);
        uint64_t x0 = _f.x0;
        _result = f0(x0, *l1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 lst_rec(T1 f, F1 &&f0, const lst &l) {
    return lst_rect<T1>(std::move(f), f0, l);
  }

  static lst range(uint64_t start, uint64_t count);
  static lst app(const lst &xs, lst ys);
  /// Two cells per step: the second is allocated and linked into the first.
  static lst stutter(const lst &xs);
};

#endif // INCLUDED_TMC_VALUE_ROOT
