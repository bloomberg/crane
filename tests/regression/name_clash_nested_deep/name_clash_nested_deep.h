#ifndef INCLUDED_NAME_CLASH_NESTED_DEEP
#define INCLUDED_NAME_CLASH_NESTED_DEEP

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct NameClashNestedDeep {
  /// Deep nesting of pattern matches to stress name generation.
  /// Each level creates d_a0, d_a00, d_a01, etc.
  struct mylist {
    // TYPES
    struct MyNil {};

    struct MyCons {
      unsigned int d_a0;
      std::shared_ptr<mylist> d_a1;
    };

    using variant_t = std::variant<MyNil, MyCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit mylist(MyNil _v) : d_v_(_v) {}

    explicit mylist(MyCons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mylist> mynil() {
      return std::make_shared<mylist>(MyNil{});
    }

    static std::shared_ptr<mylist> mycons(unsigned int a0,
                                          const std::shared_ptr<mylist> &a1) {
      return std::make_shared<mylist>(MyCons{std::move(a0), a1});
    }

    static std::shared_ptr<mylist> mycons(unsigned int a0,
                                          std::shared_ptr<mylist> &&a1) {
      return std::make_shared<mylist>(MyCons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1,
            MapsTo<T1, unsigned int, std::shared_ptr<mylist>, T1> F1>
  static T1 mylist_rect(const T1 f, F1 &&f0, const std::shared_ptr<mylist> &m) {
    if (std::holds_alternative<typename mylist::MyNil>(m->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist::MyCons>(m->v());
      return f0(d_a0, d_a1, mylist_rect<T1>(f, f0, d_a1));
    }
  }

  template <typename T1,
            MapsTo<T1, unsigned int, std::shared_ptr<mylist>, T1> F1>
  static T1 mylist_rec(const T1 f, F1 &&f0, const std::shared_ptr<mylist> &m) {
    if (std::holds_alternative<typename mylist::MyNil>(m->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist::MyCons>(m->v());
      return f0(d_a0, d_a1, mylist_rec<T1>(f, f0, d_a1));
    }
  }

  /// Four levels of nested matching.
  __attribute__((pure)) static unsigned int
  deep4(const std::shared_ptr<mylist> &a, const std::shared_ptr<mylist> &b,
        const std::shared_ptr<mylist> &c, const std::shared_ptr<mylist> &d);
  /// Match in a let, then match on the let result.
  __attribute__((pure)) static unsigned int
  let_match_chain(const std::shared_ptr<mylist> &xs,
                  const std::shared_ptr<mylist> &ys);
  /// Matching where the same list is matched multiple times.
  __attribute__((pure)) static unsigned int
  multi_match_same(const std::shared_ptr<mylist> &xs);

  /// Nested match where inner match scrutinee is a field from outer match.
  __attribute__((pure)) static unsigned int
  nested_field_match(const std::shared_ptr<mylist> &xs);
};

#endif // INCLUDED_NAME_CLASH_NESTED_DEEP
