#ifndef INCLUDED_LOOPIFY_SELF_TEMPLATE_ARGS
#define INCLUDED_LOOPIFY_SELF_TEMPLATE_ARGS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat {
  static bool eq_dec(uint64_t n, uint64_t m);
};

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
    list(const typename List::template list<_U> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename List::template list<_U>::Nil>(
                    _other.v())) {
              return Nil{};
            } else {
              const auto &[a, l] =
                  std::get<typename List::template list<_U>::Cons>(_other.v());
              return Cons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const _U &>) {
                      return crane_convert<A>(a);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (l ? std::make_shared<typename List::template list<A>>(
                           crane_convert<typename List::template list<A>>(*l))
                     : nullptr)};
            }
          }()) {}

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
      auto _next = [&](variant_t &_v)
          -> std::shared_ptr<typename List::template list<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->l);
          }
        }
        return nullptr;
      };
      std::shared_ptr<typename List::template list<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
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

      /// _Cont_Cons: resumes after recursive call, then processes rest.
      struct _Cont_Cons {};

      using _Frame = std::variant<_Enter, _Cont_Cons>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified length: _Enter -> _Cont_Cons.
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
            _stack.emplace_back(_Cont_Cons{});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Cont_Cons>(_frame));
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
