#ifndef INCLUDED_INDUCTIVE_NAMED_LIST
#define INCLUDED_INDUCTIVE_NAMED_LIST

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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
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
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
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
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
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

struct InductiveNamedList {
  struct List_ {
    // TYPES
    struct LNil {};

    struct LCons {
      uint64_t a0;
      std::shared_ptr<List_> a1;
    };

    using variant_t = std::variant<LNil, LCons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    List_() {}

    explicit List_(LNil _v) : v_(_v) {}

    explicit List_(LCons _v) : v_(std::move(_v)) {}

    static List_ lnil() { return List_(LNil{}); }

    static List_ lcons(uint64_t a0, List_ a1) {
      return List_(LCons{a0, std::make_shared<List_>(std::move(a1))});
    }

    // MANIPULATORS
    ~List_() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<List_> {
        if (auto *_alt = std::get_if<LCons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<List_> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    List_(const List_ &) = default;
    List_ &operator=(const List_ &) = default;
    List_(List_ &&) noexcept = default;
    List_ &operator=(List_ &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, List_ &, T1 &>
  static T1 List_rect(T1 f, F1 &&f0, const List_ &l) {
    if (std::holds_alternative<typename List_::LNil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename List_::LCons>(l.v());
      return f0(a0, *a1, List_rect<T1>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, List_ &, T1 &>
  static T1 List_rec(T1 f, F1 &&f0, const List_ &l) {
    if (std::holds_alternative<typename List_::LNil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename List_::LCons>(l.v());
      return f0(a0, *a1, List_rec<T1>(std::move(f), f0, *a1));
    }
  }

  static uint64_t len(const List_ &l);
  static inline const uint64_t go =
      (len(List_::lcons(UINT64_C(1),
                        List_::lcons(UINT64_C(2), List_::lnil()))) +
       List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()).length());
};

#endif // INCLUDED_INDUCTIVE_NAMED_LIST
