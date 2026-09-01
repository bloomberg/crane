#ifndef INCLUDED_LOOPIFY_SELF_TEMPLATE_ARGS
#define INCLUDED_LOOPIFY_SELF_TEMPLATE_ARGS

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct List {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<typename List::template list<A>> l;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename _U>
    list(const typename List::template list<_U> &_other) {
      if (std::holds_alternative<typename List::template list<_U>::Nil>(
              _other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a, l] =
            std::get<typename List::template list<_U>::Cons>(_other.v());
        this->v_ = Cons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a.type() == typeid(A))
                  return std::any_cast<A>(a);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a);
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
                return std::any_cast<A>(a);
              } else
                return A(a);
            }(),
            l ? std::make_shared<typename List::template list<A>>(*l)
              : nullptr};
      }
    }

    static typename List::template list<A> nil() {
      return typename List::template list<A>(Nil{});
    }

    static typename List::template list<A> cons(A a, List::list<A> l) {
      return typename List::template list<A>(Cons{
          std::move(a),
          std::make_shared<typename List::template list<A>>(std::move(l))});
    }

    // MANIPULATORS
    ~list() {
      crane::small_vector<std::shared_ptr<typename List::template list<A>>>
          _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l) {
            _stack.push_back(std::move(_alt->l));
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

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) noexcept = default;
    list &operator=(list &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t length() const {
      const typename List::template list<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const typename List::template list<A> *_self;
      };

      /// _Resume_Cons: resumes after recursive call with _result.
      struct _Resume_Cons {};

      using _Frame = std::variant<_Enter, _Resume_Cons>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified length: _Enter -> _Resume_Cons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const typename List::template list<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename List::list<A>::Nil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] =
                std::get<typename List::list<A>::Cons>(_sv.v());
            _stack.emplace_back(_Resume_Cons{});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Cons>(_frame));
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List::list<T1> remove(F0 &&eq_dec0, const T1 &x,
                               const List::list<T1> &l);
};

struct PeanoNat {
  static bool eq_dec(uint64_t n, uint64_t m);
};

struct LoopifySelfTemplateArgs {
  static List::list<uint64_t> rm(const List::list<uint64_t> &l);
  static inline const uint64_t test =
      rm(List::template list<uint64_t>::cons(
             UINT64_C(1), List::template list<uint64_t>::nil()))
          .length();
};

template <typename T1, typename F0>
  requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
List::list<T1> List::remove(F0 &&eq_dec0, const T1 &x,
                            const List::list<T1> &l) {
  if (std::holds_alternative<typename List::list<T1>::Nil>(l.v())) {
    return List::template list<T1>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List::list<T1>::Cons>(l.v());
    if (eq_dec0(x, a0)) {
      return List::template remove<T1>(eq_dec0, x, *a1);
    } else {
      return List::template list<T1>::cons(
          a0, List::template remove<T1>(eq_dec0, x, *a1));
    }
  }
}

#endif // INCLUDED_LOOPIFY_SELF_TEMPLATE_ARGS
