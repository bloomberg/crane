#ifndef INCLUDED_CLOSURES_IN_DATA
#define INCLUDED_CLOSURES_IN_DATA

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

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
              return _args.d_a1->template fold_left<T1>(f, f(a0, _args.d_a0));
            }},
        this->v());
  }

  template <typename T1, MapsTo<T1, t_A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<T1>> { return List<T1>::nil(); },
                   [&](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<T1>> {
                     return List<T1>::cons(f(_args.d_a0),
                                           _args.d_a1->template map<T1>(f));
                   }},
        this->v());
  }
};

struct ClosuresInData {
  /// A list of functions: successor, doubling, and squaring.
  static inline const std::shared_ptr<
      List<std::function<unsigned int(unsigned int)>>>
      fn_list = List<std::function<unsigned int(unsigned int)>>::cons(
          [](unsigned int x) { return (x + 1); },
          List<std::function<unsigned int(unsigned int)>>::cons(
              [](unsigned int x) { return (x + x); },
              List<std::function<unsigned int(unsigned int)>>::cons(
                  [](unsigned int x) { return (x * x); },
                  List<std::function<unsigned int(unsigned int)>>::nil())));
  /// apply_all fns x applies every function in fns to x,
  /// returning the list of results.
  static std::shared_ptr<List<unsigned int>> apply_all(
      const std::shared_ptr<List<std::function<unsigned int(unsigned int)>>>
          &fns,
      const unsigned int x);

  /// A pair of invertible transformations: forward and backward.
  struct transform {
    std::function<unsigned int(unsigned int)> forward;
    std::function<unsigned int(unsigned int)> backward;
  };

  /// A transform that doubles via addition and halves via division.
  static inline const std::shared_ptr<transform> double_transform =
      std::make_shared<transform>(
          transform{[](unsigned int x) { return (x + x); },
                    [](unsigned int x) { return (2u ? x / 2u : 0); }});
  __attribute__((pure)) static unsigned int
  apply_forward(const std::shared_ptr<transform> &t, const unsigned int x);
  __attribute__((pure)) static unsigned int
  apply_backward(const std::shared_ptr<transform> &t, const unsigned int x);
  /// compose_all fns x folds fns left, threading x through each
  /// function in sequence.
  __attribute__((pure)) static unsigned int compose_all(
      const std::shared_ptr<List<std::function<unsigned int(unsigned int)>>>
          &fns,
      const unsigned int x);
  /// A pipeline of transformations: increment, double, then add 10.
  static inline const std::shared_ptr<
      List<std::function<unsigned int(unsigned int)>>>
      pipeline = List<std::function<unsigned int(unsigned int)>>::cons(
          [](unsigned int x) { return (x + 1u); },
          List<std::function<unsigned int(unsigned int)>>::cons(
              [](unsigned int x) { return (x * 2u); },
              List<std::function<unsigned int(unsigned int)>>::cons(
                  [](unsigned int x) { return (x + 10u); },
                  List<std::function<unsigned int(unsigned int)>>::nil())));
  /// maybe_apply mf x applies function mf to x if present,
  /// otherwise returns x unchanged.
  __attribute__((pure)) static unsigned int
  maybe_apply(const std::optional<std::function<unsigned int(unsigned int)>> mf,
              const unsigned int x);
  static inline const std::shared_ptr<List<unsigned int>> test_apply_all =
      apply_all(fn_list, 5u);
  static inline const unsigned int test_forward =
      apply_forward(double_transform, 7u);
  static inline const unsigned int test_backward =
      apply_backward(double_transform, 14u);
  static inline const unsigned int test_compose = compose_all(pipeline, 3u);
  static inline const unsigned int test_maybe_some =
      maybe_apply(std::make_optional<std::function<unsigned int(unsigned int)>>(
                      [](unsigned int x) { return (x + 1); }),
                  41u);
  static inline const unsigned int test_maybe_none = maybe_apply(
      std::optional<std::function<unsigned int(unsigned int)>>(), 42u);
};

#endif // INCLUDED_CLOSURES_IN_DATA
