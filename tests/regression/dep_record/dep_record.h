#ifndef INCLUDED_DEP_RECORD
#define INCLUDED_DEP_RECORD

#include <any>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
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
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename I>
concept Magma = requires(typename I::carrier a0, typename I::carrier a1) {
  typename I::carrier;
  { I::op(a0, a1) } -> std::convertible_to<typename I::carrier>;
};
template <typename I>concept Monoid = requires (typename I::m_carrier a0,
typename I::m_carrier a1) {
  typename I::m_carrier;
  { I::m_op(a0,
a1) } -> std::convertible_to<typename I::m_carrier>;
} && (requires {
  { I::m_id() } -> std::convertible_to<typename I::m_carrier>;
} || requires {
  { I::m_id } -> std::convertible_to<typename I::m_carrier>;
});

struct DepRecord {
  using carrier = std::any;

  struct nat_magma {
    using carrier = uint64_t;

    static uint64_t op(uint64_t a0, uint64_t a1) { return (a0 + a1); }
  };

  static_assert(Magma<nat_magma>);

  struct bool_magma {
    using carrier = bool;

    constexpr static bool op(bool a0, bool a1) { return (a0 && a1); }
  };

  static_assert(Magma<bool_magma>);
  using m_carrier = std::any;

  struct nat_monoid {
    using m_carrier = uint64_t;

    static uint64_t m_op(uint64_t a0, uint64_t a1) { return (a0 + a1); }

    static uint64_t m_id() { return UINT64_C(0); }
  };

  static_assert(Monoid<nat_monoid>);

  struct nat_mul_monoid {
    using m_carrier = uint64_t;

    static uint64_t m_op(uint64_t a0, uint64_t a1) { return (a0 * a1); }

    static uint64_t m_id() { return UINT64_C(1); }
  };

  static_assert(Monoid<nat_mul_monoid>);

  template <Monoid _tcI0>
  static typename _tcI0::m_carrier
  mfold(const List<typename _tcI0::m_carrier> &l) {
    if (std::holds_alternative<typename List<typename _tcI0::m_carrier>::Nil>(
            l.v())) {
      return _tcI0::m_id();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<typename _tcI0::m_carrier>::Cons>(l.v());
      return _tcI0::m_op(a0, mfold<_tcI0>(*a1));
    }
  }

  static inline const uint64_t test_fold_add =
      std::any_cast<uint64_t>(mfold<nat_monoid>(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(
                  UINT64_C(3),
                  List<uint64_t>::cons(UINT64_C(4), List<uint64_t>::nil()))))));
  static inline const uint64_t test_fold_mul =
      std::any_cast<uint64_t>(mfold<nat_mul_monoid>(List<uint64_t>::cons(
          UINT64_C(2),
          List<uint64_t>::cons(
              UINT64_C(3),
              List<uint64_t>::cons(UINT64_C(4), List<uint64_t>::nil())))));
  enum class Tag { TNAT, TBOOL };

  template <typename T1> static T1 tag_rect(T1 f, T1 f0, Tag t) {
    switch (t) {
    case Tag::TNAT: {
      return f;
    } break;
    case Tag::TBOOL: {
      return f0;
    } break;
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 tag_rec(T1 f, T1 f0, Tag t) {
    switch (t) {
    case Tag::TNAT: {
      return f;
    } break;
    case Tag::TBOOL: {
      return f0;
    } break;
    default:
      std::unreachable();
    }
  }

  using tag_type = std::any;

  struct Tagged {
    Tag the_tag;
    tag_type the_value;

    // ACCESSORS
    Tagged clone() const { return Tagged{this->the_tag, this->the_value}; }
  };

  static inline const Tagged tagged_nat = Tagged{Tag::TNAT, UINT64_C(42)};
  static inline const Tagged tagged_bool = Tagged{Tag::TBOOL, true};
};

#endif // INCLUDED_DEP_RECORD
