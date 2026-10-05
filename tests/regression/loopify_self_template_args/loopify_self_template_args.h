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
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t length() const {
      const typename List::template list<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const typename List::template list<A> *_self;
      };

      /// CraneCont_Cons: resumes after recursive call, then processes rest.
      struct CraneCont_Cons {};

      using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified length: CraneEnter -> CraneCont_Cons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const typename List::template list<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename List::list<A>::Nil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] =
                std::get<typename List::list<A>::Cons>(_sv.v());
            _stack.emplace_back(CraneCont_Cons{});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Cons>(_frame));
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
  static constexpr uint64_t test = UINT64_C(1);
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
