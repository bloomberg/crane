#ifndef INCLUDED_DOC_COMMENTS
#define INCLUDED_DOC_COMMENTS

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

struct DocComments {
  /// add computes the sum of two natural numbers n and m.
  /// It works by structural recursion on n.
  __attribute__((pure)) static unsigned int add(const unsigned int n,
                                                const unsigned int m);

  /// A simple pair holding two values of possibly different types.
  template <typename t_A, typename t_B> struct pair {
    /// The first element of the pair.
    t_A fst;
    /// The second element of the pair.
    t_B snd;
  }; /// mylist is a polymorphic list type.

  template <typename t_A> struct mylist {
    // TYPES
    /// The empty list.
    struct Mynil {};

    /// Cons cell: an element followed by the rest of the list.
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
        Overloaded{[&](const typename mylist<T1>::Mynil) -> T2 { return f; },
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
        Overloaded{[&](const typename mylist<T1>::Mynil) -> T2 { return f; },
                   [&](const typename mylist<T1>::Mycons _args) -> T2 {
                     return f0(_args.d_a0, _args.d_a1,
                               mylist_rec<T1, T2>(f, f0, _args.d_a1));
                   }},
        m->v());
  }

  __attribute__((pure)) static unsigned int
  no_doc_comment(const unsigned int x);

  /// The identity function: returns its argument unchanged.
  template <typename T1> static T1 identity(const T1 x) { return x; }

  /// double n returns 2 * n.
  __attribute__((pure)) static unsigned int double_(const unsigned int n);
  /// A simple color enumeration.
  enum class Color {
    /// Red color.
    e_RED,
    /// Green color.
    e_GREEN,
    /// Blue color.
    e_BLUE
  };

  template <typename T1>
  static T1 color_rect(const T1 f, const T1 f0, const T1 f1, const Color c) {
    switch (c) {
    case Color::e_RED: {
      return f;
    }
    case Color::e_GREEN: {
      return f0;
    }
    case Color::e_BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 color_rec(const T1 f, const T1 f0, const T1 f1, const Color c) {
    switch (c) {
    case Color::e_RED: {
      return f;
    }
    case Color::e_GREEN: {
      return f0;
    }
    case Color::e_BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }
};

#endif // INCLUDED_DOC_COMMENTS
