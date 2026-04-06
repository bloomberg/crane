#ifndef INCLUDED_CLOSURE_ESCAPE_MATCH
#define INCLUDED_CLOSURE_ESCAPE_MATCH

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

struct ClosureEscapeMatch {
  template <typename t_A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      t_A d_a0;
      std::shared_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit mylist(Mynil _v) : d_v_(std::move(_v)) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mylist<t_A>> mynil() {
      return std::make_shared<mylist<t_A>>(Mynil{});
    }

    static std::shared_ptr<mylist<t_A>>
    mycons(t_A a0, const std::shared_ptr<mylist<t_A>> &a1) {
      return std::make_shared<mylist<t_A>>(Mycons{std::move(a0), a1});
    }

    static std::shared_ptr<mylist<t_A>>
    mycons(t_A a0, std::shared_ptr<mylist<t_A>> &&a1) {
      return std::make_shared<mylist<t_A>>(
          Mycons{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<mylist<t_A>> mynil_uptr() {
      return std::make_unique<mylist<t_A>>(Mynil{});
    }

    static std::unique_ptr<mylist<t_A>>
    mycons_uptr(t_A a0, const std::shared_ptr<mylist<t_A>> &a1) {
      return std::make_unique<mylist<t_A>>(Mycons{std::move(a0), a1});
    }

    static std::unique_ptr<mylist<t_A>>
    mycons_uptr(t_A a0, std::shared_ptr<mylist<t_A>> &&a1) {
      return std::make_unique<mylist<t_A>>(
          Mycons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<mylist<T1>>, T2> F1>
  static T2 mylist_rect(const T2 f, F1 &&f0,
                        const std::shared_ptr<mylist<T1>> &m) {
    return std::visit(
        Overloaded{
            [&](const typename mylist<T1>::Mynil _args) -> T2 { return f; },
            [&](const typename mylist<T1>::Mycons _args) -> T2 {
              return f0(_args.d_a0, _args.d_a1,
                        mylist_rect<T1, T2>(f, f0, _args.d_a1));
            }},
        m->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<mylist<T1>>, T2> F1>
  static T2 mylist_rec(const T2 f, F1 &&f0,
                       const std::shared_ptr<mylist<T1>> &m) {
    return std::visit(
        Overloaded{
            [&](const typename mylist<T1>::Mynil _args) -> T2 { return f; },
            [&](const typename mylist<T1>::Mycons _args) -> T2 {
              return f0(_args.d_a0, _args.d_a1,
                        mylist_rec<T1, T2>(f, f0, _args.d_a1));
            }},
        m->v());
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int
  length(const std::shared_ptr<mylist<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename mylist<T1>::Mynil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename mylist<T1>::Mycons _args) -> unsigned int {
                     return (length<T1>(_args.d_a1) + 1);
                   }},
        l->v());
  }

  template <typename T1>
  static std::shared_ptr<mylist<T1>> app(const std::shared_ptr<mylist<T1>> &l1,
                                         std::shared_ptr<mylist<T1>> l2) {
    return std::visit(
        Overloaded{[&](const typename mylist<T1>::Mynil _args)
                       -> std::shared_ptr<mylist<T1>> { return std::move(l2); },
                   [&](const typename mylist<T1>::Mycons _args)
                       -> std::shared_ptr<mylist<T1>> {
                     return mylist<T1>::mycons(_args.d_a0,
                                               app<T1>(_args.d_a1, l2));
                   }},
        l1->v());
  }

  /// Return a closure wrapped in option — prevents uncurrying.
  /// The closure captures a pattern variable hd (a shared_ptr),
  /// which is an inlined _args.d_a0 inside the std::visit callback.
  __attribute__((pure)) static std::optional<std::function<std::shared_ptr<
      mylist<unsigned int>>(std::shared_ptr<mylist<unsigned int>>)>>
  make_prepender_opt(
      const std::shared_ptr<mylist<std::shared_ptr<mylist<unsigned int>>>> &l);
  /// Return a closure in a pair — prevents uncurrying.
  /// Captures pattern variables x and xs.
  __attribute__((pure)) static std::optional<
      std::function<std::pair<unsigned int, unsigned int>(std::monostate)>>
  make_pair_fn_opt(const std::shared_ptr<mylist<unsigned int>> &l);
  /// Nested matches with closures returned in option.
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  nested_closure_opt(const std::shared_ptr<mylist<unsigned int>> &a,
                     const std::shared_ptr<mylist<unsigned int>> &b);
  /// Closure stored in a product, capturing shared_ptr pattern variable.
  __attribute__((pure)) static std::pair<
      unsigned int, std::function<std::shared_ptr<mylist<unsigned int>>(
                        std::shared_ptr<mylist<unsigned int>>)>>
  closure_in_pair(
      const std::shared_ptr<mylist<std::shared_ptr<mylist<unsigned int>>>> &l);
};

#endif // INCLUDED_CLOSURE_ESCAPE_MATCH
