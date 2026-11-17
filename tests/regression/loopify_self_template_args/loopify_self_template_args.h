#ifndef INCLUDED_LOOPIFY_SELF_TEMPLATE_ARGS
#define INCLUDED_LOOPIFY_SELF_TEMPLATE_ARGS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
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

    template <typename CraneU>
    list(const typename List::template list<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<
                    typename List::template list<CraneU>::Nil>(_other.v())) {
              return Nil{};
            } else {
              const auto &[a, l] =
                  std::get<typename List::template list<CraneU>::Cons>(
                      _other.v());
              return Cons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
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
      return typename List::template list<A>(
          Cons{std::move(a),
               std::make_shared<typename List::template list<A>>(std::move(l))});
    }

    // MANIPULATORS
    ~list() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next =
          [&](variant_t &_v) -> std::shared_ptr<typename List::template list<A>> {
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
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t length() const {
      const typename List::template list<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of length: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const typename List::template list<A> *_self;
      };

      struct _after_length_in_Cons {};

      using _frame = std::variant<_call, _after_length_in_Cons>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const typename List::template list<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename List::list<A>::Nil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[_, a1] =
                std::get<typename List::list<A>::Cons>(_sv.v());
            _stack.emplace_back(_after_length_in_Cons{});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_after_length_in_Cons>(_popped));
          _stack.pop_back();
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    }
  };

  template <typename T1, typename F0>
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
