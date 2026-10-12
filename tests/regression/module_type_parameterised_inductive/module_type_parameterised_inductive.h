#ifndef INCLUDED_MODULE_TYPE_PARAMETERISED_INDUCTIVE
#define INCLUDED_MODULE_TYPE_PARAMETERISED_INDUCTIVE

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename M>
concept T = requires {
  typename M::template tr<crane::obj>;
  typename M::template box<crane::obj>;
};

struct ModuleTypeParameterisedInductive {
  struct Impl {
    template <typename A> struct tr {
      // TYPES
      struct L {};

      struct N {
        std::shared_ptr<tr<A>> a0;
        A a1;
        std::shared_ptr<tr<A>> a2;
      };

      using variant_t = std::variant<L, N>;

    private:
      // DATA
      variant_t v_;

    public:
      // CREATORS
      tr() {}

      explicit tr(L _v) : v_(_v) {}

      explicit tr(N _v) : v_(std::move(_v)) {}

      template <typename CraneU>
      tr(const tr<CraneU> &_other)
          : v_([&]() -> variant_t {
              if (std::holds_alternative<typename tr<CraneU>::L>(_other.v())) {
                return L{};
              } else {
                const auto &[a0, a1, a2] =
                    std::get<typename tr<CraneU>::N>(_other.v());
                return N{
                    (a0 ? std::make_shared<tr<A>>(crane_convert<tr<A>>(*a0))
                        : nullptr),
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a1);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    (a2 ? std::make_shared<tr<A>>(crane_convert<tr<A>>(*a2))
                        : nullptr)};
              }
            }()) {}

      static tr<A> l() { return tr<A>(L{}); }

      static tr<A> n(tr<A> a0, A a1, tr<A> a2) {
        return tr<A>(N{std::make_shared<tr<A>>(std::move(a0)), std::move(a1),
                       std::make_shared<tr<A>>(std::move(a2))});
      }

      // MANIPULATORS
      ~tr() {
        if (std::holds_alternative<L>(v_mut())) {
          return;
        }
        if (auto *_alt = std::get_if<N>(&v_mut())) {
          if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
                (_alt->a2 && _alt->a2.use_count() == 1))) {
            return;
          }
        }
        crane::small_vector<std::shared_ptr<tr<A>>> _stack = {};
        auto _drain = [&](variant_t &_v) {
          if (auto *_alt = std::get_if<N>(&_v)) {
            if (_alt->a0 && _alt->a0.use_count() == 1) {
              _stack.push_back(std::move(_alt->a0));
            }
            if (_alt->a2 && _alt->a2.use_count() == 1) {
              _stack.push_back(std::move(_alt->a2));
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

      tr(const tr &) = default;
      tr &operator=(const tr &) = default;
      tr(tr &&) = default;
      tr &operator=(tr &&) = default;

      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }
    };

    template <typename T1, typename T2, typename F1>
    static T2 tr_rect(T2 f, F1 &&f0, const tr<T1> &t) {
      if (std::holds_alternative<typename tr<T1>::L>(t.v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tr<T1>::N>(t.v());
        return f0(*a0, tr_rect<T1, T2>(f, f0, *a0), a1, *a2,
                  tr_rect<T1, T2>(f, f0, *a2));
      }
    }

    template <typename T1, typename T2, typename F1>
    static T2 tr_rec(T2 f, F1 &&f0, const tr<T1> &t) {
      return tr_rect<T1, T2>(std::move(f), f0, t);
    }

    template <typename A> struct box {
      A unbox;

      // ACCESSORS
      template <typename CraneU> operator box<CraneU>() const {
        return {[&]() -> CraneU {
          if constexpr (crane_convertible<CraneU, const A &>) {
            return crane_convert<CraneU>(unbox);
          } else {
            throw std::logic_error("unreachable: inactive constructor field at "
                                   "this instantiation");
          }
        }()};
      }
    };
  };

  template <T X> struct Use {
    template <typename T1>
    static uint64_t size(const typename X::template tr<T1> &t) {
      if (std::holds_alternative<typename X::template tr<T1>::L>(t.v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename X::template tr<T1>::N>(t.v());
        return ((size<T1>(*a0) + size<T1>(*a2)) + 1);
      }
    }

    static uint64_t get(const typename X::template box<uint64_t> &b) {
      return (b.unbox + 1);
    }
  };

  using U = Use<Impl>;
  static inline const uint64_t result =
      (U::template size<uint64_t>(Impl::template tr<uint64_t>::n(
           Impl::template tr<uint64_t>::l(), UINT64_C(1),
           Impl::template tr<uint64_t>::l())) +
       U::get(Impl::box<uint64_t>{UINT64_C(4)}));
};

#endif // INCLUDED_MODULE_TYPE_PARAMETERISED_INDUCTIVE
