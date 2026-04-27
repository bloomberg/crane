#ifndef INCLUDED_REUSE_ALIAS
#define INCLUDED_REUSE_ALIAS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ReuseAlias {
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
            d_a0, d_a1
                      ? std::make_unique<ReuseAlias::mylist<t_A>>(d_a1->clone())
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

  /// Increment the head — candidate for reuse optimization when use_count = 1.
  __attribute__((pure)) static mylist<unsigned int>
  inc_head(const mylist<unsigned int> &l);
  /// Use the same list twice: once through inc_head, once directly.
  /// If reuse fires on the first call (because evaluation order is
  /// unspecified), the second use of l sees the already-mutated list.
  __attribute__((
      pure)) static std::pair<mylist<unsigned int>, mylist<unsigned int>>
  double_use(mylist<unsigned int> l);
  /// Pass the same list to two different functions.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  double_call(const mylist<unsigned int> &l);
  /// Alias through let-binding, then use both the alias and the original
  /// in a match.
  __attribute__((pure)) static std::pair<mylist<unsigned int>, unsigned int>
  alias_and_match(mylist<unsigned int> l);
  /// Build a result that refers to the scrutinee AND a pattern variable
  /// from the same match.
  __attribute__((
      pure)) static std::pair<mylist<unsigned int>, mylist<unsigned int>>
  scrutinee_in_branch(mylist<unsigned int> l);

  /// Chain inc_head: each call might try to reuse.
  __attribute__((pure)) static mylist<unsigned int>
  triple_inc(const mylist<unsigned int> &l);
};

#endif // INCLUDED_REUSE_ALIAS
