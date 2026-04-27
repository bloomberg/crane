#ifndef INCLUDED_CLOSURE_ESCAPE_MATCH
#define INCLUDED_CLOSURE_ESCAPE_MATCH

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ClosureEscapeMatch {
  template <typename t_A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      t_A d_a0;
      std::unique_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    mylist(const mylist<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    mylist<t_A> &operator=(const mylist<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    mylist<t_A> &operator=(mylist<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) mylist<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Mynil>(_sv.v())) {
        return mylist<t_A>(Mynil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Mycons>(_sv.v());
        return mylist<t_A>(Mycons{
            d_a0, d_a1 ? std::make_unique<ClosureEscapeMatch::mylist<t_A>>(
                             d_a1->clone())
                       : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        d_v_ = Mynil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        d_v_ = Mycons{t_A(d_a0),
                      d_a1 ? std::make_unique<mylist<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static mylist<t_A> mynil() { return mylist(Mynil{}); }

    __attribute__((pure)) static mylist<t_A> mycons(t_A a0,
                                                    const mylist<t_A> &a1) {
      return mylist(Mycons{std::move(a0), std::make_unique<mylist<t_A>>(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, mylist<T1>, T2> F1>
  static T2 mylist_rect(const T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(d_a0, *(d_a1), mylist_rect<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1, mylist<T1>, T2> F1>
  static T2 mylist_rec(const T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(d_a0, *(d_a1), mylist_rec<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int length(const mylist<T1> &l) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(l.v());
      return (length<T1>(*(d_a1)) + 1);
    }
  }

  template <typename T1>
  __attribute__((pure)) static mylist<T1> app(const mylist<T1> &l1,
                                              mylist<T1> l2) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l1.v())) {
      return l2;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(l1.v());
      return mylist<T1>::mycons(d_a0, app<T1>(*(d_a1), l2));
    }
  }

  /// Return a closure wrapped in option — prevents uncurrying.
  /// The closure captures a pattern variable hd (a shared_ptr),
  /// which is an inlined _args.d_a0 inside the std::visit callback.
  __attribute__((pure)) static std::optional<
      std::function<mylist<unsigned int>(mylist<unsigned int>)>>
  make_prepender_opt(const mylist<mylist<unsigned int>> &l);
  /// Return a closure in a pair — prevents uncurrying.
  /// Captures pattern variables x and xs.
  __attribute__((pure)) static std::optional<
      std::function<std::pair<unsigned int, unsigned int>(std::monostate)>>
  make_pair_fn_opt(const mylist<unsigned int> &l);
  /// Nested matches with closures returned in option.
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  nested_closure_opt(const mylist<unsigned int> &a,
                     const mylist<unsigned int> &b);
  /// Closure stored in a product, capturing shared_ptr pattern variable.
  __attribute__((pure)) static std::pair<
      unsigned int, std::function<mylist<unsigned int>(mylist<unsigned int>)>>
  closure_in_pair(const mylist<mylist<unsigned int>> &l);
};

#endif // INCLUDED_CLOSURE_ESCAPE_MATCH
