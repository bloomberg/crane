#ifndef INCLUDED_PARTIAL_APPLY
#define INCLUDED_PARTIAL_APPLY

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
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

  template <typename T1, MapsTo<T1, T1, t_A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    return std::visit(
        Overloaded{
            [&](const typename List<t_A>::Nil _args) -> T1 { return a0; },
            [&](const typename List<t_A>::Cons _args) -> T1 {
              t_A b = _args.d_a0;
              std::shared_ptr<List<t_A>> l0 = _args.d_a1;
              return std::move(l0)->template fold_left<T1>(f, f(a0, b));
            }},
        this->v());
  }

  template <typename T1, MapsTo<T1, t_A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil _args)
                -> std::shared_ptr<List<T1>> { return List<T1>::ctor::Nil_(); },
            [&](const typename List<t_A>::Cons _args)
                -> std::shared_ptr<List<T1>> {
              t_A a = _args.d_a0;
              std::shared_ptr<List<t_A>> l0 = _args.d_a1;
              return List<T1>::ctor::Cons_(f(a),
                                           std::move(l0)->template map<T1>(f));
            }},
        this->v());
  }
};

struct PartialApply {
  static std::shared_ptr<List<unsigned int>>
  inc_all(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  tag_all(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::optional<unsigned int>>>
  wrap_all(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::function<std::shared_ptr<List<unsigned int>>(
      std::shared_ptr<List<unsigned int>>)>>>
  prepend_each(const std::shared_ptr<List<unsigned int>> &l);

  template <typename t_A> struct tagged {
    // TYPES
    struct Tag {
      unsigned int d_a0;
      t_A d_a1;
    };

    using variant_t = std::variant<Tag>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit tagged(Tag _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<tagged<t_A>> Tag_(unsigned int a0, t_A a1) {
        return std::shared_ptr<tagged<t_A>>(new tagged<t_A>(Tag{a0, a1}));
      }

      static std::unique_ptr<tagged<t_A>> Tag_uptr(unsigned int a0, t_A a1) {
        return std::unique_ptr<tagged<t_A>>(new tagged<t_A>(Tag{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, unsigned int, T1> F0>
  static T2 tagged_rect(F0 &&f, const std::shared_ptr<tagged<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tagged<T1>::Tag _args) -> T2 {
          unsigned int n = _args.d_a0;
          T1 a = _args.d_a1;
          return f(std::move(n), a);
        }},
        t->v());
  }

  template <typename T1, typename T2, MapsTo<T2, unsigned int, T1> F0>
  static T2 tagged_rec(F0 &&f, const std::shared_ptr<tagged<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tagged<T1>::Tag _args) -> T2 {
          unsigned int n = _args.d_a0;
          T1 a = _args.d_a1;
          return f(std::move(n), a);
        }},
        t->v());
  }

  static std::shared_ptr<List<std::shared_ptr<tagged<bool>>>>
  tag_with(const unsigned int n, const std::shared_ptr<List<bool>> &l);
  static std::shared_ptr<
      List<std::pair<unsigned int, std::pair<unsigned int, unsigned int>>>>
  double_tag(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  sum_with_init(const unsigned int init,
                const std::shared_ptr<List<unsigned int>> &l);
  static inline const std::shared_ptr<List<unsigned int>> test_inc =
      inc_all(List<unsigned int>::ctor::Cons_(
          1u, List<unsigned int>::ctor::Cons_(
                  2u, List<unsigned int>::ctor::Cons_(
                          3u, List<unsigned int>::ctor::Nil_()))));
  static inline const std::shared_ptr<
      List<std::pair<unsigned int, unsigned int>>>
      test_tag = tag_all(List<unsigned int>::ctor::Cons_(
          10u, List<unsigned int>::ctor::Cons_(
                   20u, List<unsigned int>::ctor::Cons_(
                            30u, List<unsigned int>::ctor::Nil_()))));
  static inline const std::shared_ptr<List<std::optional<unsigned int>>>
      test_wrap = wrap_all(List<unsigned int>::ctor::Cons_(
          5u, List<unsigned int>::ctor::Cons_(
                  6u, List<unsigned int>::ctor::Cons_(
                          7u, List<unsigned int>::ctor::Nil_()))));
  static inline const std::shared_ptr<List<std::shared_ptr<tagged<bool>>>>
      test_tag_with = tag_with(
          99u, List<bool>::ctor::Cons_(
                   true, List<bool>::ctor::Cons_(
                             false, List<bool>::ctor::Cons_(
                                        true, List<bool>::ctor::Nil_()))));
  static inline const unsigned int test_sum = sum_with_init(
      100u, List<unsigned int>::ctor::Cons_(
                1u, List<unsigned int>::ctor::Cons_(
                        2u, List<unsigned int>::ctor::Cons_(
                                3u, List<unsigned int>::ctor::Nil_()))));
};

#endif // INCLUDED_PARTIAL_APPLY
