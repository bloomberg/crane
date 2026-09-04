#ifndef INCLUDED_DEP_MATCH_UNIT_VEC
#define INCLUDED_DEP_MATCH_UNIT_VEC

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
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

    template <typename _U> vec(const vec<_U> &_other) {
      if (std::holds_alternative<typename vec<_U>::Vnil>(_other.v())) {
        this->v_ = Vnil{};
      } else {
        const auto &[n, a1, a2] = std::get<typename vec<_U>::Vcons>(_other.v());
        this->v_ = Vcons{n,
                         [&]() -> A {
                           if constexpr (std::is_same_v<_U, std::any>) {
                             return crane_any_cast<A>(a1);
                           } else {
                             return A(a1);
                           }
                         }(),
                         (a2 ? std::make_shared<vec<A>>(*a2) : nullptr)};
      }
    }

    static vec<A> vnil() { return vec<A>(Vnil{}); }

    static vec<A> vcons(uint64_t n, A a1, vec<A> a2) {
      return vec<A>(
          Vcons{n, std::move(a1), std::make_shared<vec<A>>(std::move(a2))});
    }

    // MANIPULATORS
    ~vec() {
      crane::small_vector<std::shared_ptr<vec<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Vcons>(&_v)) {
          if (_alt->a2) {
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

    vec(const vec &) = default;
    vec &operator=(const vec &) = default;
    vec(vec &&) noexcept = default;
    vec &operator=(vec &&) noexcept = default;

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
      return f0(n0, a1, *a2, vec_rect<T1, T2>(f, f0, n0, *a2));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, uint64_t &, T1 &, vec<T1> &, T2 &>
  static T2 vec_rec(T2 f, F1 &&f0, uint64_t, const vec<T1> &v) {
    if (std::holds_alternative<typename vec<T1>::Vnil>(v.v())) {
      return f;
    } else {
      const auto &[n0, a1, a2] = std::get<typename vec<T1>::Vcons>(v.v());
      return f0(n0, a1, *a2, vec_rec<T1, T2>(f, f0, n0, *a2));
    }
  }

  static uint64_t head(uint64_t _x, const vec<uint64_t> &v);
  static inline const uint64_t go =
      head(UINT64_C(0), vec<uint64_t>::vcons(UINT64_C(0), UINT64_C(5),
                                             vec<uint64_t>::vnil()));
};

#endif // INCLUDED_DEP_MATCH_UNIT_VEC
