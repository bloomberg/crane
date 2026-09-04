#ifndef INCLUDED_LIST_OF_LIST_DRAIN
#define INCLUDED_LIST_OF_LIST_DRAIN

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct ListOfListDrain {
  template <typename A> struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::shared_ptr<lst<A>> a1;
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

    template <typename _U> lst(const lst<_U> &_other) {
      if (std::holds_alternative<typename lst<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename lst<_U>::Cons>(_other.v());
        this->v_ = Cons{[&]() -> A {
                          if constexpr (std::is_same_v<_U, std::any>)
                            return crane_any_cast<A>(a0);
                          else
                            return A(a0);
                        }(),
                        a1 ? std::make_shared<lst<A>>(*a1) : nullptr};
      }
    }

    static lst<A> nil() { return lst<A>(Nil{}); }

    static lst<A> cons(A a0, lst<A> a1) {
      return lst<A>(
          Cons{std::move(a0), std::make_shared<lst<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
      crane::small_vector<std::shared_ptr<lst<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
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

    lst(const lst &) = default;
    lst &operator=(const lst &) = default;
    lst(lst &&) noexcept = default;
    lst &operator=(lst &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, lst<A> &, T1 &>
    T1 lst_rec(T1 f, F1 &&f0) const {
      const lst<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const lst<A> *_self;
      };

      /// _Resume_Cons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Cons {
        lst<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Cons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified lst_rec: _Enter -> _Resume_Cons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const lst<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename lst<A>::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename lst<A>::Cons>(_sv.v());
            _stack.emplace_back(_Resume_Cons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Cons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, lst<A> &, T1 &>
    T1 lst_rect(T1 f, F1 &&f0) const {
      const lst<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const lst<A> *_self;
      };

      /// _Resume_Cons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Cons {
        lst<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Cons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified lst_rect: _Enter -> _Resume_Cons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const lst<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename lst<A>::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename lst<A>::Cons>(_sv.v());
            _stack.emplace_back(_Resume_Cons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Cons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }
  };

  struct t {
    // TYPES
    struct Node {
      uint64_t a0;
      std::shared_ptr<lst<lst<t>>> a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(Node _v) : v_(std::move(_v)) {}

    static t node(uint64_t a0, lst<lst<t>> a1) {
      return t(Node{a0, std::make_shared<lst<lst<t>>>(std::move(a1))});
    }

    // MANIPULATORS
    ~t() {
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            crane::small_vector<
                std::shared_ptr<ListOfListDrain::lst<ListOfListDrain::lst<t>>>>
                _hw1;
            if (auto *_ha10 = std::get_if<typename ListOfListDrain::lst<
                    ListOfListDrain::lst<t>>::Cons>(&((*(_alt->a1))).v_mut())) {
              crane::small_vector<std::shared_ptr<ListOfListDrain::lst<t>>>
                  _hw11;
              if (auto *_ha15 =
                      std::get_if<typename ListOfListDrain::lst<t>::Cons>(
                          &(_ha10->a0).v_mut())) {
                _stack.push_back(std::make_shared<t>(std::move(_ha15->a0)));
                _hw11.push_back(std::move(_ha15->a1));
              }
              while (!_hw11.empty()) {
                auto _hw11p = std::move(_hw11.back());
                _hw11.pop_back();
                if (!_hw11p || _hw11p.use_count() != 1) {
                  continue;
                }
                std::atomic_thread_fence(std::memory_order_acquire);
                auto &_hw11e = *_hw11p;
                if (auto *_ha13 =
                        std::get_if<typename ListOfListDrain::lst<t>::Cons>(
                            &(_hw11e).v_mut())) {
                  _stack.push_back(std::make_shared<t>(std::move(_ha13->a0)));
                  _hw11.push_back(std::move(_ha13->a1));
                }
              }
              _hw1.push_back(std::move(_ha10->a1));
            }
            while (!_hw1.empty()) {
              auto _hw1p = std::move(_hw1.back());
              _hw1.pop_back();
              if (!_hw1p || _hw1p.use_count() != 1) {
                continue;
              }
              std::atomic_thread_fence(std::memory_order_acquire);
              auto &_hw1e = *_hw1p;
              if (auto *_ha3 = std::get_if<typename ListOfListDrain::lst<
                      ListOfListDrain::lst<t>>::Cons>(&(_hw1e).v_mut())) {
                crane::small_vector<std::shared_ptr<ListOfListDrain::lst<t>>>
                    _hw4;
                if (auto *_ha8 =
                        std::get_if<typename ListOfListDrain::lst<t>::Cons>(
                            &(_ha3->a0).v_mut())) {
                  _stack.push_back(std::make_shared<t>(std::move(_ha8->a0)));
                  _hw4.push_back(std::move(_ha8->a1));
                }
                while (!_hw4.empty()) {
                  auto _hw4p = std::move(_hw4.back());
                  _hw4.pop_back();
                  if (!_hw4p || _hw4p.use_count() != 1) {
                    continue;
                  }
                  std::atomic_thread_fence(std::memory_order_acquire);
                  auto &_hw4e = *_hw4p;
                  if (auto *_ha6 =
                          std::get_if<typename ListOfListDrain::lst<t>::Cons>(
                              &(_hw4e).v_mut())) {
                    _stack.push_back(std::make_shared<t>(std::move(_ha6->a0)));
                    _hw4.push_back(std::move(_ha6->a1));
                  }
                }
                _hw1.push_back(std::move(_ha3->a1));
              }
            }
            _alt->a1.reset();
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

    t(const t &) = default;
    t &operator=(const t &) = default;
    t(t &&) noexcept = default;
    t &operator=(t &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    t wrap(uint64_t k) const {
      return t::node(
          k, lst<lst<t>>::cons(lst<t>::cons(std::move(*this), lst<t>::nil()),
                               lst<lst<t>>::nil()));
    }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, lst<lst<t>> &>
  static T1 t_rect(F0 &&f, const t &t0) {
    const auto &[a0, a1] = std::get<typename t::Node>(t0.v());
    return f(a0, *a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, lst<lst<t>> &>
  static T1 t_rec(F0 &&f, const t &t0) {
    const auto &[a0, a1] = std::get<typename t::Node>(t0.v());
    return f(a0, *a1);
  }

  static inline const t empty = t::node(UINT64_C(0), lst<lst<t>>::nil());
};

#endif // INCLUDED_LIST_OF_LIST_DRAIN
