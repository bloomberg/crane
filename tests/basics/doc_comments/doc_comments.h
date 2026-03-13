#ifndef INCLUDED_DOC_COMMENTS
#define INCLUDED_DOC_COMMENTS

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

struct DocComments {
  /// add computes the sum of two natural numbers n and m.
  /// It works by structural recursion on n.
  __attribute__((pure)) static unsigned int add(const unsigned int n,
                                                const unsigned int m);

  /// A simple pair holding two values of possibly different types.
  template <typename t_A, typename t_B> struct pair {
    t_A fst;
    t_B snd;
  };

  /// mylist is a polymorphic list type.
  /// - mynil is the empty list.
  /// - mycons prepends an element.
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

    // CREATORS
    explicit mylist(Mynil _v) : d_v_(std::move(_v)) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<mylist<t_A>> Mynil_() {
        return std::shared_ptr<mylist<t_A>>(new mylist<t_A>(Mynil{}));
      }

      static std::shared_ptr<mylist<t_A>>
      Mycons_(t_A a0, const std::shared_ptr<mylist<t_A>> &a1) {
        return std::shared_ptr<mylist<t_A>>(new mylist<t_A>(Mycons{a0, a1}));
      }

      static std::unique_ptr<mylist<t_A>> Mynil_uptr() {
        return std::unique_ptr<mylist<t_A>>(new mylist<t_A>(Mynil{}));
      }

      static std::unique_ptr<mylist<t_A>>
      Mycons_uptr(t_A a0, const std::shared_ptr<mylist<t_A>> &a1) {
        return std::unique_ptr<mylist<t_A>>(new mylist<t_A>(Mycons{a0, a1}));
      }
    };

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
              T1 y = _args.d_a0;
              std::shared_ptr<mylist<T1>> m0 = _args.d_a1;
              return f0(y, m0, mylist_rect<T1, T2>(f, f0, m0));
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
              T1 y = _args.d_a0;
              std::shared_ptr<mylist<T1>> m0 = _args.d_a1;
              return f0(y, m0, mylist_rec<T1, T2>(f, f0, m0));
            }},
        m->v());
  }

  __attribute__((pure)) static unsigned int
  no_doc_comment(const unsigned int x);

  /// The identity function: returns its argument unchanged.
  template <typename T1> static T1 identity(const T1 x) { return x; }

  /// double n returns 2 * n.
  __attribute__((pure)) static unsigned int double_(const unsigned int n);
};

#endif // INCLUDED_DOC_COMMENTS
