#ifndef INCLUDED_DEEP_APP
#define INCLUDED_DEEP_APP

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct DeepApp {
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

    template <typename CraneU>
    mylist(const mylist<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename mylist<CraneU>::Mynil>(
                    _other.v())) {
              return Mynil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename mylist<CraneU>::Mycons>(_other.v());
              return Mycons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<mylist<A>>(
                            crane_convert<mylist<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    static mylist<A> mycons(A a0, crane::shared_child_slot<mylist<A>> a1) {
      return mylist<A>(Mycons{std::move(a0), a1.take()});
    }

    // MANIPULATORS
    ~mylist() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
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
    mylist(mylist &&) = default;
    mylist &operator=(mylist &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 mylist_rect(T2 f, F1 &&f0, const mylist<T1> &m) {
    // Explicit stack replaces the non-tail recursion of mylist_rect: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const mylist<T1> *m;
    };

    struct _after_mylist_rect_in_Mycons {
      T1 a0;
      std::shared_ptr<mylist<T1>> a1;
    };

    using _frame = std::variant<_call, _after_mylist_rect_in_Mycons>;
    T2 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&m});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const mylist<T1> &m = *_f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
          _stack.emplace_back(_after_mylist_rect_in_Mycons{a0, a1});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_mylist_rect_in_Mycons>(_popped));
        _stack.pop_back();
        auto a0 = std::move(_f.a0);
        std::shared_ptr<mylist<T1>> a1 = std::move(_f.a1);
        _result = f0(a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
  static T2 mylist_rec(T2 f, F1 &&f0, const mylist<T1> &m) {
    return mylist_rect<T1, T2>(std::move(f), f0, m);
  }

  /// Tail-recursive builder — loopified.
  static mylist<uint64_t> build(uint64_t n, mylist<uint64_t> acc);

  /// Recursive app — NOT tail-recursive, so loopification won't help
  /// unless TMC kicks in.  Even with TMC, the destructor chain for
  /// the result is still deep.
  template <typename T1>
  static mylist<T1> app(const mylist<T1> &l1, mylist<T1> l2) {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<mylist<T1>> _root{};
    std::shared_ptr<mylist<T1>> *_write = nullptr;
    const mylist<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename mylist<T1>::Mynil>(_loop_l1->v())) {
        auto _value = std::move(l2);
        (_write ? *(*_write = std::make_shared<mylist<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<T1>::Mycons>(_loop_l1->v());
        auto _cell = typename mylist<T1>::Mycons(a0, nullptr);
        mylist<T1> &_node = (
            _write ? *(*_write = std::make_shared<mylist<T1>>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
        _write = &std::get<typename mylist<T1>::Mycons>(_node.v_mut()).a1;
        _loop_l1 = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }

  /// Recursive map — same issue.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const T1 &>
  static mylist<T2> map(F0 &&f, const mylist<T1> &l) {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<mylist<T2>> _root{};
    std::shared_ptr<mylist<T2>> *_write = nullptr;
    const mylist<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename mylist<T1>::Mynil>(_loop_l->v())) {
        auto _value = mylist<T2>::mynil();
        (_write ? *(*_write = std::make_shared<mylist<T2>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<T1>::Mycons>(_loop_l->v());
        auto _cell = typename mylist<T2>::Mycons(f(a0), nullptr);
        mylist<T2> &_node = (
            _write ? *(*_write = std::make_shared<mylist<T2>>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
        _write = &std::get<typename mylist<T2>::Mycons>(_node.v_mut()).a1;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }

  /// Identity map to force traversal.
  static mylist<uint64_t> map_id(const mylist<uint64_t> &l);
  /// Append two lists.
  static mylist<uint64_t> append_lists(const mylist<uint64_t> &x0_,
                                       mylist<uint64_t> x1_);
  static uint64_t head_or_zero(const mylist<uint64_t> &l);

  template <typename T1> static uint64_t length(const mylist<T1> &l) {
    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const mylist<T1> *l;
    };

    struct _after_length_in_Mycons {};

    using _frame = std::variant<_call, _after_length_in_Mycons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const mylist<T1> &l = *_f.l;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename mylist<T1>::Mycons>(l.v());
          _stack.emplace_back(_after_length_in_Mycons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_Mycons>(_popped));
        _stack.pop_back();
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

#endif // INCLUDED_DEEP_APP
