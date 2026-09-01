#ifndef INCLUDED_LIST_OF_PROD_DEEP
#define INCLUDED_LIST_OF_PROD_DEEP

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct ListOfProdDeep {
  template <typename A> struct lst {
    // TYPES
    struct Lnil {};

    struct Lcons {
      A a0;
      std::shared_ptr<lst<A>> a1;
    };

    using variant_t = std::variant<Lnil, Lcons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    lst() {}

    explicit lst(Lnil _v) : v_(_v) {}

    explicit lst(Lcons _v) : v_(std::move(_v)) {}

    template <typename _U> lst(const lst<_U> &_other) {
      if (std::holds_alternative<typename lst<_U>::Lnil>(_other.v())) {
        this->v_ = Lnil{};
      } else {
        const auto &[a0, a1] = std::get<typename lst<_U>::Lcons>(_other.v());
        this->v_ = Lcons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<lst<A>>(*a1) : nullptr};
      }
    }

    static lst<A> lnil() { return lst<A>(Lnil{}); }

    static lst<A> lcons(A a0, lst<A> a1) {
      return lst<A>(
          Lcons{std::move(a0), std::make_shared<lst<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
      crane::small_vector<std::shared_ptr<lst<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Lcons>(&_v)) {
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

      /// _Resume_Lcons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Lcons {
        lst<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Lcons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified lst_rec: _Enter -> _Resume_Lcons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const lst<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename lst<A>::Lnil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename lst<A>::Lcons>(_sv.v());
            _stack.emplace_back(_Resume_Lcons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Lcons>(_frame));
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

      /// _Resume_Lcons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Lcons {
        lst<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Lcons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified lst_rect: _Enter -> _Resume_Lcons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const lst<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename lst<A>::Lnil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename lst<A>::Lcons>(_sv.v());
            _stack.emplace_back(_Resume_Lcons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Lcons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }
  };

  struct t {
    // TYPES
    struct Node {
      std::shared_ptr<lst<std::pair<t, uint64_t>>> a0;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(Node _v) : v_(std::move(_v)) {}

    static t node(lst<std::pair<t, uint64_t>> a0) {
      return t(
          Node{std::make_shared<lst<std::pair<t, uint64_t>>>(std::move(a0))});
    }

    // MANIPULATORS
    ~t() {
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            crane::small_vector<
                std::shared_ptr<ListOfProdDeep::lst<std::pair<t, uint64_t>>>>
                _hw1;
            if (auto *_ha5 = std::get_if<typename ListOfProdDeep::lst<
                    std::pair<t, uint64_t>>::Lcons>(&((*(_alt->a0))).v_mut())) {
              _stack.push_back(
                  std::make_shared<t>(std::move((_ha5->a0).first)));
              _hw1.push_back(std::move(_ha5->a1));
            }
            while (!_hw1.empty()) {
              auto _hw1p = std::move(_hw1.back());
              _hw1.pop_back();
              if (!_hw1p || _hw1p.use_count() != 1) {
                continue;
              }
              std::atomic_thread_fence(std::memory_order_acquire);
              auto &_hw1e = *_hw1p;
              if (auto *_ha3 = std::get_if<typename ListOfProdDeep::lst<
                      std::pair<t, uint64_t>>::Lcons>(&(_hw1e).v_mut())) {
                _stack.push_back(
                    std::make_shared<t>(std::move((_ha3->a0).first)));
                _hw1.push_back(std::move(_ha3->a1));
              }
            }
            _alt->a0.reset();
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
      return t::node(lst<std::pair<t, uint64_t>>::lcons(
          std::make_pair(std::move(*this), k),
          lst<std::pair<t, uint64_t>>::lnil()));
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, lst<std::pair<t, uint64_t>> &>
    T1 t_rec(F0 &&f) const {
      const auto &[a0] = std::get<typename t::Node>(this->v());
      return f(*a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, lst<std::pair<t, uint64_t>> &>
    T1 t_rect(F0 &&f) const {
      const auto &[a0] = std::get<typename t::Node>(this->v());
      return f(*a0);
    }
  };

  static inline const t empty = t::node(lst<std::pair<t, uint64_t>>::lnil());
};

#endif // INCLUDED_LIST_OF_PROD_DEEP
