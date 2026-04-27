#ifndef INCLUDED_NAME_CLASH_NESTED_DEEP
#define INCLUDED_NAME_CLASH_NESTED_DEEP

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct NameClashNestedDeep {
  /// Deep nesting of pattern matches to stress name generation.
  /// Each level creates d_a0, d_a00, d_a01, etc.
  struct mylist {
    // TYPES
    struct MyNil {};

    struct MyCons {
      unsigned int d_a0;
      std::unique_ptr<mylist> d_a1;
    };

    using variant_t = std::variant<MyNil, MyCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(MyNil _v) : d_v_(_v) {}

    explicit mylist(MyCons _v) : d_v_(std::move(_v)) {}

    mylist(const mylist &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) mylist &operator=(const mylist &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) mylist &operator=(mylist &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) mylist clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<MyNil>(_sv.v())) {
        return mylist(MyNil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<MyCons>(_sv.v());
        return mylist(MyCons{
            [](auto &&__v) -> unsigned int {
              if constexpr (
                  requires { __v ? 0 : 0; } && requires { *__v; } &&
                  requires { __v->clone(); } && requires { __v.get(); }) {
                using _E = std::remove_cvref_t<decltype(*__v)>;
                return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
              } else if constexpr (requires { __v.clone(); }) {
                return __v.clone();
              } else {
                return __v;
              }
            }(d_a0),
            d_a1 ? std::make_unique<NameClashNestedDeep::mylist>(d_a1->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static mylist mynil() { return mylist(MyNil{}); }

    __attribute__((pure)) static mylist mycons(unsigned int a0,
                                               const mylist &a1) {
      return mylist(MyCons{std::move(a0), std::make_unique<mylist>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) mylist *operator->() { return this; }

    __attribute__((pure)) const mylist *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = mylist(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F1>
  static T1 mylist_rect(const T1 f, F1 &&f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::MyNil>(m.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist::MyCons>(m.v());
      return f0(d_a0, *(d_a1), mylist_rect<T1>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F1>
  static T1 mylist_rec(const T1 f, F1 &&f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::MyNil>(m.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist::MyCons>(m.v());
      return f0(d_a0, *(d_a1), mylist_rec<T1>(f, f0, *(d_a1)));
    }
  }

  /// Four levels of nested matching.
  __attribute__((pure)) static unsigned int
  deep4(const mylist &a, const mylist &b, const mylist &c, const mylist &d);
  /// Match in a let, then match on the let result.
  __attribute__((pure)) static unsigned int let_match_chain(const mylist &xs,
                                                            const mylist &ys);
  /// Matching where the same list is matched multiple times.
  __attribute__((pure)) static unsigned int multi_match_same(const mylist &xs);
  /// Nested match where inner match scrutinee is a field from outer match.
  __attribute__((pure)) static unsigned int
  nested_field_match(const mylist &xs);
};

#endif // INCLUDED_NAME_CLASH_NESTED_DEEP
