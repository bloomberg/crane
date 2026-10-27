#ifndef INCLUDED_LOOPIFY_RECEIVER_FROM_TEMPORARY
#define INCLUDED_LOOPIFY_RECEIVER_FROM_TEMPORARY

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

/// A tail-recursive method whose recursive call passes, as the receiver, a
/// binder of a match on a value the turn makes.
///
/// The loop keeps the receiver as a pointer, _loop_self.  A receiver made
/// in the turn must be parked in a local outliving the loop first, and the
/// C++ reading that decided this saw only receivers spelled as temporaries:
/// inner is a reference into the result of wrap, so the loop pointed at
/// it, and the next turn read it after that result was destroyed -- a
/// heap-use-after-free.  The turns whose receiver no parameter of the loop
/// gives are now the recursion plan's ({!Control_ir.rebuilt}), and these
/// park.
struct LoopifyReceiverFromTemporary {
  template <typename A> struct box {
    // DATA
    A a0;

    // ACCESSORS
    box<A> clone() const { return {a0}; }

    template <typename CraneU> operator box<CraneU>() const {
      return {[&]() -> CraneU {
        if constexpr (crane_convertible<CraneU, const A &>) {
          return crane_convert<CraneU>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }

    // CREATORS
    static box<A> b(A a0) { return {std::move(a0)}; }

    template <typename T1, typename F0> T1 box_rec(F0 &&f) const {
      return this->template box_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const A &>
    T1 box_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  };

  struct t {
    // TYPES
    struct L {};

    struct N {
      std::shared_ptr<box<t>> a0;
    };

    using variant_t = std::variant<L, N>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(L _v) : v_(_v) {}

    explicit t(N _v) : v_(std::move(_v)) {}

    static t l() { return t(L{}); }

    static t n(box<t> a0) {
      return t(N{std::make_shared<box<t>>(std::move(a0))});
    }

    // MANIPULATORS
    ~t() {
      if (std::holds_alternative<L>(v_mut())) {
        return;
      }
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<N>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _stack.push_back(std::make_shared<t>(std::move(_alt->a0->a0)));
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
    t(t &&) = default;
    t &operator=(t &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t walk(uint64_t n, uint64_t k) const {
      t _self_store;
      const t *_loop_self = this;
      uint64_t _loop_n = n;
      uint64_t _loop_k = k;
      while (true) {
        if (_loop_n <= 0) {
          return _loop_k;
        } else {
          uint64_t m = _loop_n - 1;
          auto &&_sv = _loop_self->wrap();
          if (std::holds_alternative<typename t::L>(_sv.v())) {
            return _loop_k;
          } else {
            const auto &[a0] = std::get<typename t::N>(_sv.v());
            const auto &_sv0 = *a0;
            const auto &[a00] = _sv0;
            _self_store = a00;
            _loop_self = &_self_store;
            _loop_n = m;
            _loop_k = (_loop_k + 1);
          }
        }
      }
    }

    t wrap() const { return t::n(box<t>::b(t::n(box<t>::b(*this)))); }

    template <typename T1, typename F1> T1 t_rec(T1 f, F1 &&f0) const {
      return this->template t_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 t_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename t::L>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename t::N>(this->v());
        return f0(*a0);
      }
    }
  };

  static uint64_t go(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_RECEIVER_FROM_TEMPORARY
