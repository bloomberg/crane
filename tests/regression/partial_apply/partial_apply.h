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
  template <typename T1, MapsTo<T1, A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> std::shared_ptr<List<T1>> {
              return List<T1>::ctor::nil_();
            },
            [&](const typename List<A>::cons _args)
                -> std::shared_ptr<List<T1>> {
              A a = _args._a0;
              std::shared_ptr<List<A>> l0 = _args._a1;
              return List<T1>::ctor::cons_(f(a),
                                           std::move(l0)->template map<T1>(f));
            }},
        this->v());
  }
  template <typename T1, MapsTo<T1, T1, A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    return std::visit(
        Overloaded{[&](const typename List<A>::nil _args) -> T1 { return a0; },
                   [&](const typename List<A>::cons _args) -> T1 {
                     A b = _args._a0;
                     std::shared_ptr<List<A>> l0 = _args._a1;
                     return std::move(l0)->template fold_left<T1>(f, f(a0, b));
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

  template <typename A> struct tagged {
  public:
    struct Tag {
      unsigned int _a0;
      A _a1;
    };
    using variant_t = std::variant<Tag>;

  private:
    variant_t v_;
    explicit tagged(Tag _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<tagged<A>> Tag_(unsigned int a0, A a1) {
        return std::shared_ptr<tagged<A>>(new tagged<A>(Tag{a0, a1}));
      }
      static std::unique_ptr<tagged<A>> Tag_uptr(unsigned int a0, A a1) {
        return std::unique_ptr<tagged<A>>(new tagged<A>(Tag{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, unsigned int, T1> F0>
  static T2 tagged_rect(F0 &&f, const std::shared_ptr<tagged<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tagged<T1>::Tag _args) -> T2 {
          unsigned int n = _args._a0;
          T1 a = _args._a1;
          return f(std::move(n), a);
        }},
        t->v());
  }

  template <typename T1, typename T2, MapsTo<T2, unsigned int, T1> F0>
  static T2 tagged_rec(F0 &&f, const std::shared_ptr<tagged<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tagged<T1>::Tag _args) -> T2 {
          unsigned int n = _args._a0;
          T1 a = _args._a1;
          return f(std::move(n), a);
        }},
        t->v());
  }

  static std::shared_ptr<List<std::shared_ptr<tagged<bool>>>>
  tag_with(const unsigned int n, const std::shared_ptr<List<bool>> &l);

  static std::shared_ptr<
      List<std::pair<unsigned int, std::pair<unsigned int, unsigned int>>>>
  double_tag(const std::shared_ptr<List<unsigned int>> &l);

  static unsigned int
  sum_with_init(const unsigned int init,
                const std::shared_ptr<List<unsigned int>> &l);

  static inline const std::shared_ptr<List<unsigned int>> test_inc =
      inc_all(List<unsigned int>::ctor::cons_(
          (0 + 1), List<unsigned int>::ctor::cons_(
                       ((0 + 1) + 1), List<unsigned int>::ctor::cons_(
                                          (((0 + 1) + 1) + 1),
                                          List<unsigned int>::ctor::nil_()))));

  static inline const std::shared_ptr<
      List<std::pair<unsigned int, unsigned int>>>
      test_tag = tag_all(List<unsigned int>::ctor::cons_(
          ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
          List<unsigned int>::ctor::cons_(
              ((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1),
              List<unsigned int>::ctor::cons_(
                  ((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) +
                                           1) +
                                          1) +
                                         1) +
                                        1) +
                                       1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1),
                  List<unsigned int>::ctor::nil_()))));

  static inline const std::shared_ptr<List<std::optional<unsigned int>>>
      test_wrap = wrap_all(List<unsigned int>::ctor::cons_(
          (((((0 + 1) + 1) + 1) + 1) + 1),
          List<unsigned int>::ctor::cons_(
              ((((((0 + 1) + 1) + 1) + 1) + 1) + 1),
              List<unsigned int>::ctor::cons_(
                  (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                  List<unsigned int>::ctor::nil_()))));

 static inline const std::shared_ptr<List<std::shared_ptr<tagged<bool>>>> test_tag_with = tag_with((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), List<bool>::ctor::cons_(true, List<bool>::ctor::cons_(false, List<bool>::ctor::cons_(true, List<bool>::ctor::nil_()))));

 static inline const unsigned int test_sum = sum_with_init(((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), List<unsigned int>::ctor::cons_((0 + 1), List<unsigned int>::ctor::cons_(((0 + 1) + 1), List<unsigned int>::ctor::cons_((((0 + 1) + 1) + 1), List<unsigned int>::ctor::nil_()))));
};
