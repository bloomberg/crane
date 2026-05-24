#ifndef INCLUDED_SEPEXTQUALIFIEDRAW
#define INCLUDED_SEPEXTQUALIFIEDRAW

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

namespace SepExtQualifiedRaw {

template <typename M>
concept OrderedType = requires { typename M::t; };

template <OrderedType X> struct Make {
  template <typename A> struct Fmap {
    // TYPES
    struct Empty {};

    struct Node {
      typename X::t a0;
      A a1;
      std::shared_ptr<Fmap<A>> a2;
    };

    using variant_t = std::variant<Empty, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Fmap() {}

    explicit Fmap(Empty _v) : v_(_v) {}

    explicit Fmap(Node _v) : v_(std::move(_v)) {}

    template <typename _U> explicit Fmap(const Fmap<_U> &_other) {
      if (std::holds_alternative<typename Fmap<_U>::Empty>(_other.v())) {
        this->v_ = Empty{};
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename Fmap<_U>::Node>(_other.v());
        this->v_ = Node{
            a0,
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a1.type() == typeid(A))
                  return std::any_cast<A>(a1);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a1);
                  return A{
                      [&]() -> typename A::first_type {
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
                return std::any_cast<A>(a1);
              } else
                return A(a1);
            }(),
            a2 ? std::make_shared<Fmap<A>>(*a2) : nullptr};
      }
    }

    static Fmap<A> empty() { return Fmap(Empty{}); }

    static Fmap<A> node(typename X::t a0, A a1, Fmap<A> a2) {
      return Fmap(Node{std::move(a0), std::move(a1),
                       std::make_shared<Fmap<A>>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, typename X::t &, T1 &, Fmap<T1> &,
                                   T2 &>
  static T2 fmap_rect(T2 f, F1 &&f0, const Fmap<T1> &f1) {
    if (std::holds_alternative<typename Fmap<T1>::Empty>(f1.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename Fmap<T1>::Node>(f1.v());
      return f0(a0, a1, *a2, fmap_rect<T1, T2>(f, f0, *a2));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, typename X::t &, T1 &, Fmap<T1> &,
                                   T2 &>
  static T2 fmap_rec(T2 f, F1 &&f0, const Fmap<T1> &f1) {
    if (std::holds_alternative<typename Fmap<T1>::Empty>(f1.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename Fmap<T1>::Node>(f1.v());
      return f0(a0, a1, *a2, fmap_rec<T1, T2>(f, f0, *a2));
    }
  }

  template <typename T1> static bool is_empty(const Fmap<T1> &m) {
    if (std::holds_alternative<typename Fmap<T1>::Empty>(m.v())) {
      return true;
    } else {
      return false;
    }
  }
};

} // namespace SepExtQualifiedRaw

#endif // INCLUDED_SEPEXTQUALIFIEDRAW
