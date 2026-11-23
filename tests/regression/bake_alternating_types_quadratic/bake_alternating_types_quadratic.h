#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

#include "crane_bake.h"
extern const crane::bake::image crane_baked_big_4b4779b0641d;

struct BakeAlternatingTypesQuadratic {
  struct mterm;
  struct mlist;

  struct mterm {
    // TYPES
    struct MLit {
      uint64_t a0;
    };

    struct MAdd {
      std::shared_ptr<mterm> a0;
      std::shared_ptr<mlist> a1;
    };

    using variant_t = std::variant<MLit, MAdd>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mterm() {}

    explicit mterm(MLit _v) : v_(std::move(_v)) {}

    explicit mterm(MAdd _v) : v_(std::move(_v)) {}

    static mterm mlit(uint64_t a0) { return mterm(MLit{a0}); }

    static mterm madd(crane::shared_child_slot<mterm> a0, mlist a1) {
      return mterm(MAdd{a0.take(), std::make_shared<mlist>(std::move(a1))});
    }

    // MANIPULATORS
    ~mterm() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<MAdd>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<mterm>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<mlist>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename mlist::MCons>(&_pv)) {
                if (_alt->a0 && _alt->a0.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1 && _alt->a1.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
            }
          }
        }
      }
    }

    mterm(const mterm &) = default;
    mterm &operator=(const mterm &) = default;
    mterm(mterm &&) = default;
    mterm &operator=(mterm &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct mlist {
    // TYPES
    struct MNil {};

    struct MCons {
      std::shared_ptr<mterm> a0;
      std::shared_ptr<mlist> a1;
    };

    using variant_t = std::variant<MNil, MCons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mlist() {}

    explicit mlist(MNil _v) : v_(_v) {}

    explicit mlist(MCons _v) : v_(std::move(_v)) {}

    static mlist mnil() { return mlist(MNil{}); }

    static mlist mcons(mterm a0, crane::shared_child_slot<mlist> a1) {
      return mlist(MCons{std::make_shared<mterm>(std::move(a0)), a1.take()});
    }

    // MANIPULATORS
    ~mlist() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<MCons>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<mlist>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<mterm>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename mterm::MAdd>(&_pv)) {
                if (_alt->a0 && _alt->a0.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1 && _alt->a1.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
            }
          }
        }
      }
    }

    mlist(const mlist &) = default;
    mlist &operator=(const mlist &) = default;
    mlist(mlist &&) = default;
    mlist &operator=(mlist &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 mterm_rect(F0 &&f, F1 &&f0, const mterm &m) {
    // Explicit stack replaces the non-tail recursion of mterm_rect: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const mterm *m;
    };

    struct _after_mterm_rect_in_MAdd {
      std::shared_ptr<mterm> a0;
      std::shared_ptr<mlist> a1;
    };

    using _frame = std::variant<_call, _after_mterm_rect_in_MAdd>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const mterm &m = *_f.m;
        if (std::holds_alternative<typename mterm::MLit>(m.v())) {
          const auto &[a0] = std::get<typename mterm::MLit>(m.v());
          _result = f(a0);
        } else {
          const auto &[a0, a1] = std::get<typename mterm::MAdd>(m.v());
          _stack.emplace_back(_after_mterm_rect_in_MAdd{a0, a1});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else {
        auto _f = std::move(std::get<_after_mterm_rect_in_MAdd>(_popped));
        _stack.pop_back();
        std::shared_ptr<mterm> a0 = std::move(_f.a0);
        std::shared_ptr<mlist> a1 = std::move(_f.a1);
        _result = f0(*a0, std::move(_result), *a1);
      }
    }
    return _result;
  }

  template <typename T1, typename F0, typename F1>
  static T1 mterm_rec(F0 &&f, F1 &&f0, const mterm &m) {
    return mterm_rect<T1>(f, f0, m);
  }

  template <typename T1, typename F1>
  static T1 mlist_rect(T1 f, F1 &&f0, const mlist &m) {
    // Explicit stack replaces the non-tail recursion of mlist_rect: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const mlist *m;
    };

    struct _after_mlist_rect_in_MCons {
      std::shared_ptr<mterm> a0;
      std::shared_ptr<mlist> a1;
    };

    using _frame = std::variant<_call, _after_mlist_rect_in_MCons>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const mlist &m = *_f.m;
        if (std::holds_alternative<typename mlist::MNil>(m.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename mlist::MCons>(m.v());
          _stack.emplace_back(_after_mlist_rect_in_MCons{a0, a1});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_mlist_rect_in_MCons>(_popped));
        _stack.pop_back();
        std::shared_ptr<mterm> a0 = std::move(_f.a0);
        std::shared_ptr<mlist> a1 = std::move(_f.a1);
        _result = f0(*a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 mlist_rec(T1 f, F1 &&f0, const mlist &m) {
    return mlist_rect<T1>(std::move(f), f0, m);
  }

  static mterm alt(uint64_t n);
  static inline const mterm big =
      crane::bake::read<mterm>(crane_baked_big_4b4779b0641d);
  static inline const uint64_t result = []() {
    auto &&_sv = big;
    if (std::holds_alternative<typename mterm::MLit>(_sv.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, _] = std::get<typename mterm::MAdd>(_sv.v());
      auto &&_sv0 = *a0;
      if (std::holds_alternative<typename mterm::MLit>(_sv0.v())) {
        const auto &[a00] = std::get<typename mterm::MLit>(_sv0.v());
        return a00;
      } else {
        return UINT64_C(0);
      }
    }
  }();
};
