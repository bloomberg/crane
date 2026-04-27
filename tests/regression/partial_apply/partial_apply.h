#ifndef INCLUDED_PARTIAL_APPLY
#define INCLUDED_PARTIAL_APPLY

#include <functional>
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
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, T1, t_A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (*(d_a1)).template fold_left<T1>(f, f(a0, d_a0));
    }
  }

  template <typename T1, MapsTo<T1, t_A> F0>
  __attribute__((pure)) List<T1> map(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<T1>::cons(f(d_a0), (*(d_a1)).template map<T1>(f));
    }
  }
};

struct PartialApply {
  __attribute__((pure)) static List<unsigned int>
  inc_all(const List<unsigned int> &l);
  __attribute__((pure)) static List<std::pair<unsigned int, unsigned int>>
  tag_all(const List<unsigned int> &l);
  __attribute__((pure)) static List<std::optional<unsigned int>>
  wrap_all(const List<unsigned int> &l);
  __attribute__((
      pure)) static List<std::function<List<unsigned int>(List<unsigned int>)>>
  prepend_each(const List<unsigned int> &l);

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

  public:
    // CREATORS
    tagged() {}

    explicit tagged(Tag _v) : d_v_(std::move(_v)) {}

    tagged(const tagged<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tagged(tagged<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    tagged<t_A> &operator=(const tagged<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tagged<t_A> &operator=(tagged<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tagged<t_A> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Tag>(_sv.v());
      return tagged<t_A>(Tag{d_a0, d_a1});
    }

    // CREATORS
    template <typename _U> explicit tagged(const tagged<_U> &_other) {
      const auto &[d_a0, d_a1] = std::get<typename tagged<_U>::Tag>(_other.v());
      d_v_ = Tag{d_a0, t_A(d_a1)};
    }

    __attribute__((pure)) static tagged<t_A> tag(unsigned int a0, t_A a1) {
      return tagged(Tag{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, unsigned int, T1> F0>
  static T2 tagged_rect(F0 &&f, const tagged<T1> &t) {
    const auto &[d_a0, d_a1] = std::get<typename tagged<T1>::Tag>(t.v());
    return f(d_a0, d_a1);
  }

  template <typename T1, typename T2, MapsTo<T2, unsigned int, T1> F0>
  static T2 tagged_rec(F0 &&f, const tagged<T1> &t) {
    const auto &[d_a0, d_a1] = std::get<typename tagged<T1>::Tag>(t.v());
    return f(d_a0, d_a1);
  }

  __attribute__((pure)) static List<tagged<bool>> tag_with(unsigned int n,
                                                           const List<bool> &l);
  __attribute__((pure)) static List<
      std::pair<unsigned int, std::pair<unsigned int, unsigned int>>>
  double_tag(const List<unsigned int> &l);
  __attribute__((pure)) static unsigned int
  sum_with_init(const unsigned int &init, const List<unsigned int> &l);
  static inline const List<unsigned int> test_inc =
      inc_all(List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))));
  static inline const List<std::pair<unsigned int, unsigned int>> test_tag =
      tag_all(List<unsigned int>::cons(
          10u,
          List<unsigned int>::cons(
              20u, List<unsigned int>::cons(30u, List<unsigned int>::nil()))));
  static inline const List<std::optional<unsigned int>> test_wrap =
      wrap_all(List<unsigned int>::cons(
          5u,
          List<unsigned int>::cons(
              6u, List<unsigned int>::cons(7u, List<unsigned int>::nil()))));
  static inline const List<tagged<bool>> test_tag_with = tag_with(
      99u, List<bool>::cons(
               true, List<bool>::cons(
                         false, List<bool>::cons(true, List<bool>::nil()))));
  static inline const unsigned int test_sum =
      sum_with_init(100u, List<unsigned int>::cons(
                              1u, List<unsigned int>::cons(
                                      2u, List<unsigned int>::cons(
                                              3u, List<unsigned int>::nil()))));
};

#endif // INCLUDED_PARTIAL_APPLY
