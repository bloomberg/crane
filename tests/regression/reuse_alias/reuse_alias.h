#ifndef INCLUDED_REUSE_ALIAS
#define INCLUDED_REUSE_ALIAS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct ReuseAlias {
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

  /// Increment the head — candidate for reuse optimization when use_count = 1.
  static std::shared_ptr<mylist<unsigned int>>
  inc_head(const std::shared_ptr<mylist<unsigned int>> &l);
  /// Use the same list twice: once through inc_head, once directly.
  /// If reuse fires on the first call (because evaluation order is
  /// unspecified), the second use of l sees the already-mutated list.
  __attribute__((pure)) static std::pair<std::shared_ptr<mylist<unsigned int>>,
                                         std::shared_ptr<mylist<unsigned int>>>
  double_use(std::shared_ptr<mylist<unsigned int>> l);
  /// Pass the same list to two different functions.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  double_call(std::shared_ptr<mylist<unsigned int>> l);
  /// Alias through let-binding, then use both the alias and the original
  /// in a match.
  __attribute__((pure)) static std::pair<std::shared_ptr<mylist<unsigned int>>,
                                         unsigned int>
  alias_and_match(std::shared_ptr<mylist<unsigned int>> l);
  /// Build a result that refers to the scrutinee AND a pattern variable
  /// from the same match.
  __attribute__((pure)) static std::pair<std::shared_ptr<mylist<unsigned int>>,
                                         std::shared_ptr<mylist<unsigned int>>>
  scrutinee_in_branch(std::shared_ptr<mylist<unsigned int>> l);

  /// Chain inc_head: each call might try to reuse.
  static std::shared_ptr<mylist<unsigned int>>
  triple_inc(const std::shared_ptr<mylist<unsigned int>> &l);
};

#endif // INCLUDED_REUSE_ALIAS
