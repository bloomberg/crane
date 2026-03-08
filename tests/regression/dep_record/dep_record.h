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

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

template <typename I>
concept Magma = requires(typename I::carrier a0, typename I::carrier a1) {
  typename I::carrier;
  { I::op(a1, a0) } -> std::convertible_to<typename I::carrier>;
};
template <typename I>
concept Monoid = (requires (typename I::m_carrier a0, typename I::m_carrier a1) {
  typename I::m_carrier;
  { I::m_op(a1, a0) } -> std::convertible_to<typename I::m_carrier>;
} && (requires {
  { I::m_id() } -> std::convertible_to<typename I::m_carrier>;
} || requires {
  { I::m_id } -> std::convertible_to<typename I::m_carrier>;
}));

struct DepRecord {
  using carrier = std::any;

  struct nat_magma {
    using carrier = unsigned int;
    static unsigned int op(unsigned int a0, unsigned int a1) {
      return (a0 + a1);
    }
  };
  static_assert(Magma<nat_magma>);

  struct bool_magma {
    using carrier = bool;
    static bool op(bool a0, bool a1) { return (a0 && a1); }
  };
  static_assert(Magma<bool_magma>);

  using m_carrier = std::any;

  struct nat_monoid {
    using m_carrier = unsigned int;
    static unsigned int m_op(unsigned int a0, unsigned int a1) {
      return (a0 + a1);
    }
    static unsigned int m_id() { return 0u; }
  };
  static_assert(Monoid<nat_monoid>);

  struct nat_mul_monoid {
    using m_carrier = unsigned int;
    static unsigned int m_op(unsigned int a0, unsigned int a1) {
      return (a0 * a1);
    }
    static unsigned int m_id() { return 1u; }
  };
  static_assert(Monoid<nat_mul_monoid>);

  template <typename _tcI0, typename m_carrier>
  static m_carrier mfold(const std::shared_ptr<List<m_carrier>> &l) {
    return std::visit(
        Overloaded{
            [&](const typename List<m_carrier>::nil _args) -> m_carrier {
              return _tcI0::m_id();
            },
            [&](const typename List<m_carrier>::cons _args) -> m_carrier {
              m_carrier x = _args._a0;
              std::shared_ptr<List<m_carrier>> rest = _args._a1;
              return _tcI0::m_op(x, mfold<_tcI0, m_carrier>(rest));
            }},
        l->v());
  }

  static inline const unsigned int test_fold_add =
      mfold<nat_monoid>(List<unsigned int>::ctor::cons_(
          1u, List<unsigned int>::ctor::cons_(
                  2u, List<unsigned int>::ctor::cons_(
                          3u, List<unsigned int>::ctor::cons_(
                                  4u, List<unsigned int>::ctor::nil_())))));

  static inline const unsigned int test_fold_mul =
      mfold<nat_mul_monoid>(List<unsigned int>::ctor::cons_(
          2u, List<unsigned int>::ctor::cons_(
                  3u, List<unsigned int>::ctor::cons_(
                          4u, List<unsigned int>::ctor::nil_()))));

  enum class tag { TNat, TBool };

  template <typename T1>
  static T1 tag_rect(const T1 f, const T1 f0, const tag t) {
    return [&](void) {
      switch (t) {
      case tag::TNat: {
        return f;
      }
      case tag::TBool: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 tag_rec(const T1 f, const T1 f0, const tag t) {
    return [&](void) {
      switch (t) {
      case tag::TNat: {
        return f;
      }
      case tag::TBool: {
        return f0;
      }
      }
    }();
  }

  using tag_type = std::any;

  struct Tagged {
    tag the_tag;
    tag_type the_value;
  };

  static inline const std::shared_ptr<Tagged> tagged_nat =
      std::make_shared<Tagged>(Tagged{tag::TNat, 42u});

  static inline const std::shared_ptr<Tagged> tagged_bool =
      std::make_shared<Tagged>(Tagged{tag::TBool, true});
};
