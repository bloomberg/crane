#ifndef INCLUDED_DEP_RECORD
#define INCLUDED_DEP_RECORD

#include <any>
#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename I>
concept Magma = requires(typename I::carrier a0, typename I::carrier a1) {
  typename I::carrier;
  { I::op(a0, a1) } -> std::convertible_to<typename I::carrier>;
};
template <typename I>
concept Monoid = requires (typename I::m_carrier a0, typename I::m_carrier
a1) {
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
    using carrier = unsigned int;

    __attribute__((pure)) static unsigned int op(unsigned int a0,
                                                 unsigned int a1) {
      return (a0 + a1);
    }
  };

  static_assert(Magma<nat_magma>);

  struct bool_magma {
    using carrier = bool;

    __attribute__((pure)) static bool op(bool a0, bool a1) {
      return (a0 && a1);
    }
  };

  static_assert(Magma<bool_magma>);
  using m_carrier = std::any;

  struct nat_monoid {
    using m_carrier = unsigned int;

    __attribute__((pure)) static unsigned int m_op(unsigned int a0,
                                                   unsigned int a1) {
      return (a0 + a1);
    }

    __attribute__((pure)) static unsigned int m_id() { return 0u; }
  };

  static_assert(Monoid<nat_monoid>);

  struct nat_mul_monoid {
    using m_carrier = unsigned int;

    __attribute__((pure)) static unsigned int m_op(unsigned int a0,
                                                   unsigned int a1) {
      return (a0 * a1);
    }

    __attribute__((pure)) static unsigned int m_id() { return 1u; }
  };

  static_assert(Monoid<nat_mul_monoid>);

  template <Monoid _tcI0>
  __attribute__((pure)) static typename _tcI0::m_carrier
  mfold(const List<typename _tcI0::m_carrier> &l) {
    if (std::holds_alternative<typename List<typename _tcI0::m_carrier>::Nil>(
            l.v())) {
      return _tcI0::m_id();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<typename _tcI0::m_carrier>::Cons>(l.v());
      return _tcI0::m_op(d_a0, mfold<_tcI0>(*(d_a1)));
    }
  }

  static inline const unsigned int test_fold_add =
      std::any_cast<unsigned int>(mfold<nat_monoid>(List<unsigned int>::cons(
          1u, List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(
                          3u, List<unsigned int>::cons(
                                  4u, List<unsigned int>::nil()))))));
  static inline const unsigned int test_fold_mul = std::any_cast<unsigned int>(
      mfold<nat_mul_monoid>(List<unsigned int>::cons(
          2u,
          List<unsigned int>::cons(
              3u, List<unsigned int>::cons(4u, List<unsigned int>::nil())))));
  enum class Tag { e_TNAT, e_TBOOL };

  template <typename T1>
  static T1 tag_rect(const T1 f, const T1 f0, const Tag t) {
    switch (t) {
    case Tag::e_TNAT: {
      return f;
    }
    case Tag::e_TBOOL: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 tag_rec(const T1 f, const T1 f0, const Tag t) {
    switch (t) {
    case Tag::e_TNAT: {
      return f;
    }
    case Tag::e_TBOOL: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  using tag_type = std::any;

  struct Tagged {
    Tag the_tag;
    tag_type the_value;

    __attribute__((pure)) Tagged *operator->() { return this; }

    __attribute__((pure)) const Tagged *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Tagged clone() const {
      return Tagged{(*(this)).the_tag, (*(this)).the_value};
    }
  };

  static inline const Tagged tagged_nat = Tagged{Tag::e_TNAT, 42u};
  static inline const Tagged tagged_bool = Tagged{Tag::e_TBOOL, true};
};

#endif // INCLUDED_DEP_RECORD
