#ifndef INCLUDED_DEPENDENT_EXTRACTION_TARGETS
#define INCLUDED_DEPENDENT_EXTRACTION_TARGETS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
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
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
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

struct DependentExtractionTargets {
  struct Inner {
    struct t {
      // TYPES
      struct A {};

      struct B {
        uint64_t a0;
      };

      using variant_t = std::variant<A, B>;

    private:
      // DATA
      variant_t v_;

    public:
      // CREATORS
      t() {}

      explicit t(A _v) : v_(_v) {}

      explicit t(B _v) : v_(std::move(_v)) {}

      static t a() { return t(A{}); }

      static t b(uint64_t a0) { return t(B{a0}); }

      // MANIPULATORS
      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }
    };

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, const uint64_t &>
    static T1 t_rect(T1 f0, F1 &&f1, const t &t0) {
      if (std::holds_alternative<typename t::A>(t0.v())) {
        return f0;
      } else {
        const auto &[a0] = std::get<typename t::B>(t0.v());
        return f1(a0);
      }
    }

    template <typename T1, typename F1>
    static T1 t_rec(T1 f0, F1 &&f1, const t &t0) {
      return t_rect<T1>(std::move(f0), f1, t0);
    }

    static uint64_t f(const t &x);

    struct Deep {
      static inline const uint64_t g = f(t::b(UINT64_C(4)));
    };
  };

  struct A {
    struct t {
      // DATA
      uint64_t a0;

      // ACCESSORS
      t clone() const { return {a0}; }

      // CREATORS
      static t t0(uint64_t a0) { return {a0}; }
    };

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    static T1 t_rect(F0 &&f0, const t &t0) {
      const auto &[a0] = t0;
      return f0(a0);
    }

    template <typename T1, typename F0> static T1 t_rec(F0 &&f0, const t &t0) {
      return t_rect<T1>(f0, t0);
    }

    static uint64_t get(const t &x);
  };

  struct B {
    static inline const uint64_t use = A::get(A::t::t0(UINT64_C(9)));
  };

  template <typename T1> static List<T1> rep(const T1 &z, uint64_t n) {
    if (n <= 0) {
      return List<T1>::nil();
    } else {
      uint64_t m = n - 1;
      return List<T1>::cons(z, rep<T1>(z, m));
    }
  }

  static inline const uint64_t result =
      ((Inner::Deep::g + B::use) +
       rep<uint64_t>(UINT64_C(7), UINT64_C(3)).length());
};

#endif // INCLUDED_DEPENDENT_EXTRACTION_TARGETS
