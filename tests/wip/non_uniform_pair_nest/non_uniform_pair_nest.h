#ifndef INCLUDED_NON_UNIFORM_PAIR_NEST
#define INCLUDED_NON_UNIFORM_PAIR_NEST

#include <any>
#include <memory>
#include <utility>
#include <variant>

struct NonUniformPairNest {
  template <typename A> struct nest {
    // TYPES
    struct NZ {
      A a0;
    };

    struct NS {
      std::shared_ptr<nest<std::pair<A, A>>> a0;
    };

    using variant_t = std::variant<NZ, NS>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    nest() {}

    explicit nest(NZ _v) : v_(std::move(_v)) {}

    explicit nest(NS _v) : v_(std::move(_v)) {}

    template <typename _U> nest(const nest<_U> &_other) {
      if (std::holds_alternative<typename nest<_U>::NZ>(_other.v())) {
        const auto &[a0] = std::get<typename nest<_U>::NZ>(_other.v());
        this->v_ = NZ{[&]() -> A {
          if constexpr (std::is_same_v<_U, std::any>) {
            if (a0.type() == typeid(A))
              return std::any_cast<A>(a0);
            if constexpr (requires {
                            typename A::first_type;
                            typename A::second_type;
                          }) {
              const auto &[_k, _v] =
                  std::any_cast<std::pair<std::any, std::any>>(a0);
              return A{[&]() -> typename A::first_type {
                         if constexpr (std::is_same_v<typename A::first_type,
                                                      std::any>)
                           return _k;
                         else
                           return std::any_cast<typename A::first_type>(_k);
                       }(),
                       [&]() -> typename A::second_type {
                         if constexpr (std::is_same_v<typename A::second_type,
                                                      std::any>)
                           return _v;
                         else
                           return std::any_cast<typename A::second_type>(_v);
                       }()};
            }
            return std::any_cast<A>(a0);
          } else
            return A(a0);
        }()};
      } else {
        const auto &[a0] = std::get<typename nest<_U>::NS>(_other.v());
        this->v_ =
            NS{a0 ? std::make_shared<nest<std::pair<A, A>>>(*a0) : nullptr};
      }
    }

    static nest<A> nz(A a0) { return nest(NZ{std::move(a0)}); }

    static nest<A> ns(nest<std::pair<A, A>> a0) {
      return nest(NS{std::make_shared<nest<std::pair<A, A>>>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0, typename F1>
  static T1 nest_rect(F0 &&f, F1 &&f0, const nest<T2> &n) {
    if (std::holds_alternative<typename nest<T2>::NZ>(n.v())) {
      const auto &[a0] = std::get<typename nest<T2>::NZ>(n.v());
      return std::any_cast<T1>(f(a0));
    } else {
      const auto &[a0] = std::get<typename nest<T2>::NS>(n.v());
      return std::any_cast<T1>(f0(*a0, nest_rect<T1, T2>(f, f0, *a0)));
    }
  }

  template <typename T1, typename T2, typename F0, typename F1>
  static T1 nest_rec(F0 &&f, F1 &&f0, const nest<T2> &n) {
    if (std::holds_alternative<typename nest<T2>::NZ>(n.v())) {
      const auto &[a0] = std::get<typename nest<T2>::NZ>(n.v());
      return std::any_cast<T1>(f(a0));
    } else {
      const auto &[a0] = std::get<typename nest<T2>::NS>(n.v());
      return std::any_cast<T1>(f0(*a0, nest_rec<T1, T2>(f, f0, *a0)));
    }
  }

  template <typename T1> static uint64_t size(const nest<T1> &n) {
    if (std::holds_alternative<typename nest<T1>::NZ>(n.v())) {
      return UINT64_C(1);
    } else {
      const auto &[a0] = std::get<typename nest<T1>::NS>(n.v());
      return (UINT64_C(2) * size<T1>(*a0));
    }
  }

  static inline const uint64_t go =
      size<uint64_t>(nest<uint64_t>::ns(nest<std::pair<uint64_t, uint64_t>>::nz(
          std::make_pair(UINT64_C(1), UINT64_C(2)))));
};

#endif // INCLUDED_NON_UNIFORM_PAIR_NEST
