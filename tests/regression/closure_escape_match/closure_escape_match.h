#ifndef INCLUDED_CLOSURE_ESCAPE_MATCH
#define INCLUDED_CLOSURE_ESCAPE_MATCH

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct ClosureEscapeMatch {
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
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
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
    mylist(mylist &&) = default;
    mylist &operator=(mylist &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 mylist_rect(T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(a0, *a1, mylist_rect<T1, T2>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 mylist_rec(const T2 &f, F1 &&f0, const mylist<T1> &m) {
    return mylist_rect<T1, T2>(f, f0, m);
  }

  template <typename T1> static uint64_t length(const mylist<T1> &l) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l.v());
      return (length<T1>(*a1) + 1);
    }
  }

  template <typename T1>
  static mylist<T1> app(const mylist<T1> &l1, mylist<T1> l2) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l1.v())) {
      return l2;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l1.v());
      return mylist<T1>::mycons(a0, app<T1>(*a1, std::move(l2)));
    }
  }

  /// Return a closure wrapped in option — prevents uncurrying.
  /// The closure captures a pattern variable hd (a shared_ptr),
  /// which is an inlined _args.d_a0 inside the std::visit callback.
  static std::optional<crane::fn<mylist<uint64_t>(mylist<uint64_t>)>>
  make_prepender_opt(const mylist<mylist<uint64_t>> &l);
  /// Return a closure in a pair — prevents uncurrying.
  /// Captures pattern variables x and xs.
  static std::optional<crane::fn<std::pair<uint64_t, uint64_t>(std::monostate)>>
  make_pair_fn_opt(const mylist<uint64_t> &l);
  /// Nested matches with closures returned in option.
  static std::optional<crane::fn<uint64_t(uint64_t)>>
  nested_closure_opt(const mylist<uint64_t> &a, const mylist<uint64_t> &b);
  /// Closure stored in a product, capturing shared_ptr pattern variable.
  static std::pair<uint64_t, crane::fn<mylist<uint64_t>(mylist<uint64_t>)>>
  closure_in_pair(const mylist<mylist<uint64_t>> &l);
};

#endif // INCLUDED_CLOSURE_ESCAPE_MATCH
