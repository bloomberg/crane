#ifndef INCLUDED_METHODIFIED_MEMBER_NAME_CLASH
#define INCLUDED_METHODIFIED_MEMBER_NAME_CLASH

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MethodifiedMemberNameClash {
  struct other {
    // TYPES
    struct O1 {};

    struct O2 {
      std::shared_ptr<other> a0;
    };

    using variant_t = std::variant<O1, O2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    other() {}

    explicit other(O1 _v) : v_(_v) {}

    explicit other(O2 _v) : v_(std::move(_v)) {}

    static other o1() { return other(O1{}); }

    static other o2(other a0) {
      return other(O2{std::make_shared<other>(std::move(a0))});
    }

    // MANIPULATORS
    ~other() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<other> {
        if (auto *_alt = std::get_if<O2>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<other> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    other(const other &) = default;
    other &operator=(const other &) = default;
    other(other &&) = default;
    other &operator=(other &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
    T1 other_rec(const T1 &f, F1 &&f0) const {
      return this->template other_rect<T1>(f, f0);
    }

    template <typename T1, typename F1> T1 other_rect(T1 f, F1 &&f0) const {
      const other *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const other *_self;
      };

      /// CraneCont_O2: saves [a0], resumes after recursive call, then processes
      /// rest.
      struct CraneCont_O2 {
        std::shared_ptr<other> a0;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_O2>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified other_rect: CraneEnter -> CraneCont_O2.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const other *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename other::O1>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0] = std::get<typename other::O2>(_sv.v());
            _stack.emplace_back(CraneCont_O2{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_O2>(_frame));
          std::shared_ptr<other> a0 = std::move(_f.a0);
          _result = f0(*a0, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct wrap {
    // TYPES
    struct W {
      other a0;
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

    static wrap w(other a0) { return wrap(W{std::move(a0)}); }

    static wrap ww(wrap a0) {
      return wrap(WW{std::make_shared<wrap>(std::move(a0))});
    }

    // MANIPULATORS
    ~wrap() {
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

    uint64_t variant_t0() const { return UINT64_C(1); }

    uint64_t v0() const { return UINT64_C(0); }

    template <typename T1, typename F0, typename F1>
    T1 wrap_rec(F0 &&f, F1 &&f0) const {
      return this->template wrap_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const other &>
    T1 wrap_rect(F0 &&f, F1 &&f0) const {
      const wrap *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const wrap *_self;
      };

      /// CraneCont_WW: saves [a0], resumes after recursive call, then processes
      /// rest.
      struct CraneCont_WW {
        std::shared_ptr<wrap> a0;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_WW>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified wrap_rect: CraneEnter -> CraneCont_WW.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const wrap *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename wrap::W>(_sv.v())) {
            const auto &[a0] = std::get<typename wrap::W>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0] = std::get<typename wrap::WW>(_sv.v());
            _stack.emplace_back(CraneCont_WW{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_WW>(_frame));
          std::shared_ptr<wrap> a0 = std::move(_f.a0);
          _result = f0(*a0, std::move(_result));
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_METHODIFIED_MEMBER_NAME_CLASH
