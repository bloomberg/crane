#ifndef INCLUDED_DEP_RECORD
#define INCLUDED_DEP_RECORD

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename I>
concept Magma = requires(typename I::carrier a0, typename I::carrier a1) {
  typename I::carrier;
  { I::op(a1, a0) } -> std::convertible_to<typename I::carrier>;
};
template <typename I>
concept Monoid = requires(typename I::m_carrier a0, typename I::m_carrier a1) {
  typename I::m_carrier;
  { I::m_op(a1, a0) } -> std::convertible_to<typename I::m_carrier>;
} && requires {
  { I::m_id() } -> std::convertible_to<typename I::m_carrier>;
} || requires {
  { I::m_id } -> std::convertible_to<typename I::m_carrier>;
};

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

  template <typename _tcI0, typename m_carrier>
  static m_carrier mfold(const std::shared_ptr<List<m_carrier>> &l) {
    return std::visit(
        Overloaded{
            [&](const typename List<m_carrier>::Nil _args) -> m_carrier {
              return _tcI0::m_id();
            },
            [&](const typename List<m_carrier>::Cons _args) -> m_carrier {
              m_carrier x = _args.d_a0;
              std::shared_ptr<List<m_carrier>> rest = _args.d_a1;
              return _tcI0::m_op(x, mfold<_tcI0, m_carrier>(rest));
            }},
        l->v());
  }

  static inline const unsigned int test_fold_add =
      mfold<nat_monoid, unsigned int>(List<unsigned int>::ctor::Cons_(
          1u, List<unsigned int>::ctor::Cons_(
                  2u, List<unsigned int>::ctor::Cons_(
                          3u, List<unsigned int>::ctor::Cons_(
                                  4u, List<unsigned int>::ctor::Nil_())))));
  static inline const unsigned int test_fold_mul =
      mfold<nat_mul_monoid, unsigned int>(List<unsigned int>::ctor::Cons_(
          2u, List<unsigned int>::ctor::Cons_(
                  3u, List<unsigned int>::ctor::Cons_(
                          4u, List<unsigned int>::ctor::Nil_()))));
  enum class Tag { e_TNAT, e_TBOOL };

  template <typename T1>
  static T1 tag_rect(const T1 f, const T1 f0, const Tag t) {
    return [&](void) {
      switch (t) {
      case Tag::e_TNAT: {
        return f;
      }
      case Tag::e_TBOOL: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 tag_rec(const T1 f, const T1 f0, const Tag t) {
    return [&](void) {
      switch (t) {
      case Tag::e_TNAT: {
        return f;
      }
      case Tag::e_TBOOL: {
        return f0;
      }
      }
    }();
  }

  using tag_type = std::any;

  struct Tagged {
    Tag the_tag;
    tag_type the_value;
  };

  static inline const std::shared_ptr<Tagged> tagged_nat =
      std::make_shared<Tagged>(Tagged{Tag::e_TNAT, 42u});
  static inline const std::shared_ptr<Tagged> tagged_bool =
      std::make_shared<Tagged>(Tagged{Tag::e_TBOOL, true});
};

#endif // INCLUDED_DEP_RECORD
