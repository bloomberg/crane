#ifndef INCLUDED_LOOPIFY_TMC_LIBRARY_INDUCTIVE
#define INCLUDED_LOOPIFY_TMC_LIBRARY_INDUCTIVE

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct Sig;
struct T;

struct Fin {
  static T of_nat_lt(uint64_t p, uint64_t n);
};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename CraneU> operator Sig<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const A &>) {
        return crane_convert<CraneU>(x);
      } else {
        throw std::logic_error("unreachable: inactive constructor field at "
                               "this instantiation");
      }
    }()};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct T {
  // TYPES
  struct F1 {
    uint64_t n;
  };

  struct FS {
    uint64_t n;
    std::shared_ptr<T> a1;
  };

  using variant_t = std::variant<F1, FS>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  T() {}

  explicit T(F1 _v) : v_(std::move(_v)) {}

  explicit T(FS _v) : v_(std::move(_v)) {}

  static T f1(uint64_t n) { return T(F1{n}); }

  static T fs(uint64_t n, T a1) {
    return T(FS{n, std::make_shared<T>(std::move(a1))});
  }

  // MANIPULATORS
  ~T() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<T> {
      if (auto *_alt = std::get_if<FS>(&_v)) {
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a1);
        }
      }
      return nullptr;
    };
    std::shared_ptr<T> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  T(const T &) = default;
  T &operator=(const T &) = default;
  T(T &&) = default;
  T &operator=(T &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Sig<uint64_t> to_nat(uint64_t _x) const {
    const T *_self = this;

    // Explicit stack replaces the non-tail recursion of to_nat: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const T *_self;
      uint64_t _x;
    };

    struct _after_to_nat_in_FS {};

    using _frame = std::variant<_call, _after_to_nat_in_FS>;
    Sig<uint64_t> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self, _x});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const T *_self = _f._self;
        uint64_t _x = _f._x;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename T::F1>(_sv.v())) {
          _result = Sig<uint64_t>::exist(UINT64_C(0));
        } else {
          const auto &[n1, a1] = std::get<typename T::FS>(_sv.v());
          _stack.emplace_back(_after_to_nat_in_FS{});
          _stack.emplace_back(_call{crane_raw(a1), n1});
        }
      } else {
        auto _f = std::move(std::get<_after_to_nat_in_FS>(_popped));
        _stack.pop_back();
        Sig<uint64_t> _tmp1 = std::move(_result);
        auto &[x0] = _tmp1;
        _result = Sig<uint64_t>::exist((std::move(x0) + 1));
      }
    }
    return _result;
  }
};

struct LoopifyTmcLibraryInductive {
  using digit = T;
  static digit digit_of_nat(uint64_t n);
  static uint64_t digit_to_nat(const T &d);
  static inline const uint64_t seven = digit_to_nat(digit_of_nat(UINT64_C(7)));
};

#endif // INCLUDED_LOOPIFY_TMC_LIBRARY_INDUCTIVE
