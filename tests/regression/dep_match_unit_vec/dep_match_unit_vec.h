#ifndef INCLUDED_DEP_MATCH_UNIT_VEC
#define INCLUDED_DEP_MATCH_UNIT_VEC

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct DepMatchUnitVec {
  template <typename A> struct vec {
    // TYPES
    struct Vnil {};

    struct Vcons {
      uint64_t n;
      A a1;
      std::shared_ptr<vec<A>> a2;
    };

    using variant_t = std::variant<Vnil, Vcons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    vec() {}

    explicit vec(Vnil _v) : v_(_v) {}

    explicit vec(Vcons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    vec(const vec<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename vec<CraneU>::Vnil>(
                    _other.v())) {
              return Vnil{};
            } else {
              const auto &[n, a1, a2] =
                  std::get<typename vec<CraneU>::Vcons>(_other.v());
              return Vcons{
                  n,
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a1);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (a2 ? std::make_shared<vec<A>>(crane_convert<vec<A>>(*a2))
                      : nullptr)};
            }
          }()) {}

    static vec<A> vnil() { return vec<A>(Vnil{}); }

    static vec<A> vcons(uint64_t n, A a1, vec<A> a2) {
      return vec<A>(
          Vcons{n, std::move(a1), std::make_shared<vec<A>>(std::move(a2))});
    }

    // MANIPULATORS
    ~vec() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<vec<A>> {
        if (auto *_alt = std::get_if<Vcons>(&_v)) {
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a2);
          }
        }
        return nullptr;
      };
      std::shared_ptr<vec<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    vec(const vec &) = default;
    vec &operator=(const vec &) = default;
    vec(vec &&) = default;
    vec &operator=(vec &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, uint64_t &, T1 &, vec<T1> &, T2 &>
  static T2 vec_rect(T2 f, F1 &&f0, uint64_t, const vec<T1> &v) {
    if (std::holds_alternative<typename vec<T1>::Vnil>(v.v())) {
      return f;
    } else {
      const auto &[n0, a1, a2] = std::get<typename vec<T1>::Vcons>(v.v());
      return f0(n0, a1, *a2, vec_rect<T1, T2>(std::move(f), f0, n0, *a2));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, uint64_t &, T1 &, vec<T1> &, T2 &>
  static T2 vec_rec(T2 f, F1 &&f0, uint64_t, const vec<T1> &v) {
    if (std::holds_alternative<typename vec<T1>::Vnil>(v.v())) {
      return f;
    } else {
      const auto &[n0, a1, a2] = std::get<typename vec<T1>::Vcons>(v.v());
      return f0(n0, a1, *a2, vec_rec<T1, T2>(std::move(f), f0, n0, *a2));
    }
  }

  static uint64_t head(uint64_t _x, const vec<uint64_t> &v);
  static inline const uint64_t go =
      head(UINT64_C(0), vec<uint64_t>::vcons(UINT64_C(0), UINT64_C(5),
                                             vec<uint64_t>::vnil()));
};

#endif // INCLUDED_DEP_MATCH_UNIT_VEC
