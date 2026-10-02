#ifndef INCLUDED_DEEP_DESTRUCT
#define INCLUDED_DEEP_DESTRUCT

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

struct DeepDestruct {
  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::shared_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    template <typename _U>
    mylist(const mylist<_U> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename mylist<_U>::Mynil>(
                    _other.v())) {
              return Mynil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename mylist<_U>::Mycons>(_other.v());
              return Mycons{[&]() -> A {
                              if constexpr (crane_convertible<A, const _U &>) {
                                return crane_convert<A>(a0);
                              } else {
                                throw std::logic_error(
                                    "unreachable: inactive constructor field "
                                    "at this instantiation");
                              }
                            }(),
                            (a1 ? std::make_shared<mylist<A>>(
                                      crane_convert<mylist<A>>(*a1))
                                : nullptr)};
            }
          }()) {}

    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist<A>(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<mylist<A>> {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<mylist<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    mylist(const mylist &) = default;
    mylist &operator=(const mylist &) = default;
    mylist(mylist &&) noexcept = default;
    mylist &operator=(mylist &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, mylist<T1> &, T2 &>
  static T2
  mylist_rect(T2 f, F1 &&f0,
              const mylist<T1> &m) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      const mylist<T1> *m;
    };

    /// _Cont_Mycons: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Mycons {
      T1 a0;
      std::shared_ptr<mylist<T1>> a1;
    };

    using _Frame = std::variant<_Enter, _Cont_Mycons>;
    T2 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&m});
    /// Loopified mylist_rect: _Enter -> _Cont_Mycons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> &m = *_f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
          _stack.emplace_back(_Cont_Mycons{a0, a1});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Mycons>(_frame));
        auto a0 = std::move(_f.a0);
        std::shared_ptr<mylist<T1>> a1 = std::move(_f.a1);
        T2 r_ = std::move(_result);
        _result = f0(a0, *a1, std::move(r_));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, mylist<T1> &, T2 &>
  static T2
  mylist_rec(T2 f, F1 &&f0,
             const mylist<T1> &m) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const mylist<T1> *m;
    };

    /// _Cont_Mycons: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Mycons {
      T1 a0;
      std::shared_ptr<mylist<T1>> a1;
    };

    using _Frame = std::variant<_Enter, _Cont_Mycons>;
    T2 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&m});
    /// Loopified mylist_rec: _Enter -> _Cont_Mycons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> &m = *_f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
          _stack.emplace_back(_Cont_Mycons{a0, a1});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Mycons>(_frame));
        auto a0 = std::move(_f.a0);
        std::shared_ptr<mylist<T1>> a1 = std::move(_f.a1);
        T2 r_ = std::move(_result);
        _result = f0(a0, *a1, std::move(r_));
      }
    }
    return _result;
  }

  /// Tail-recursive list builder — should compile to a loop.
  static mylist<uint64_t> build_aux(uint64_t n, mylist<uint64_t> acc);
  static mylist<uint64_t> build(uint64_t n);
  /// Simple accessor to observe the result.
  static uint64_t head_or_zero(const mylist<uint64_t> &l);
};

#endif // INCLUDED_DEEP_DESTRUCT
