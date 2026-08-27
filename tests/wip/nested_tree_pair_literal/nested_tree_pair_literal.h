#ifndef INCLUDED_NESTED_TREE_PAIR_LITERAL
#define INCLUDED_NESTED_TREE_PAIR_LITERAL

#include <any>
#include <memory>
#include <utility>
#include <variant>

/// WIP: A non-uniform (nested) inductive `tree A := Lf : A -> tree A | Nd :
/// tree (A * A) -> tree A` builds a literal value: the erased-parameter
/// constructor still expects `uint64_t` where a `std::pair<uint64_t, uint64_t>`
/// is supplied.
struct NestedTreePairLiteral {
  template <typename A> struct tree {
    // TYPES
    struct Lf {
      A a0;
    };

    struct Nd {
      std::shared_ptr<tree<std::pair<A, A>>> a0;
    };

    using variant_t = std::variant<Lf, Nd>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Lf _v) : v_(std::move(_v)) {}

    explicit tree(Nd _v) : v_(std::move(_v)) {}

    template <typename _U> tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Lf>(_other.v())) {
        const auto &[a0] = std::get<typename tree<_U>::Lf>(_other.v());
        this->v_ = Lf{[&]() -> A {
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
        const auto &[a0] = std::get<typename tree<_U>::Nd>(_other.v());
        this->v_ =
            Nd{a0 ? std::make_shared<tree<std::pair<A, A>>>(*a0) : nullptr};
      }
    }

    static tree<A> lf(A a0) { return tree(Lf{std::move(a0)}); }

    static tree<A> nd(tree<std::pair<A, A>> a0) {
      return tree(Nd{std::make_shared<tree<std::pair<A, A>>>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0, typename F1>
  static T1 tree_rect(F0 &&f, F1 &&f0, const tree<T2> &t) {
    if (std::holds_alternative<typename tree<T2>::Lf>(t.v())) {
      const auto &[a0] = std::get<typename tree<T2>::Lf>(t.v());
      return std::any_cast<T1>(f(a0));
    } else {
      const auto &[a0] = std::get<typename tree<T2>::Nd>(t.v());
      return std::any_cast<T1>(f0(*a0, tree_rect<T1, T2>(f, f0, *a0)));
    }
  }

  template <typename T1, typename T2, typename F0, typename F1>
  static T1 tree_rec(F0 &&f, F1 &&f0, const tree<T2> &t) {
    if (std::holds_alternative<typename tree<T2>::Lf>(t.v())) {
      const auto &[a0] = std::get<typename tree<T2>::Lf>(t.v());
      return std::any_cast<T1>(f(a0));
    } else {
      const auto &[a0] = std::get<typename tree<T2>::Nd>(t.v());
      return std::any_cast<T1>(f0(*a0, tree_rec<T1, T2>(f, f0, *a0)));
    }
  }

  template <typename T1> static uint64_t size(const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Lf>(t.v())) {
      return UINT64_C(1);
    } else {
      const auto &[a0] = std::get<typename tree<T1>::Nd>(t.v());
      return (UINT64_C(2) * size<T1>(*a0));
    }
  }

  static inline const tree<uint64_t> sample =
      tree<uint64_t>::nd(tree<std::pair<uint64_t, uint64_t>>::nd(
          tree<std::pair<std::pair<uint64_t, uint64_t>,
                         std::pair<uint64_t, uint64_t>>>::
              lf(std::make_pair(std::make_pair(UINT64_C(1), UINT64_C(2)),
                                std::make_pair(UINT64_C(3), UINT64_C(4))))));

  static inline const uint64_t go = size<uint64_t>(sample);
};

#endif // INCLUDED_NESTED_TREE_PAIR_LITERAL
