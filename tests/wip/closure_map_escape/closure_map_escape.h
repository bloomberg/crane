#ifndef INCLUDED_CLOSURE_MAP_ESCAPE
#define INCLUDED_CLOSURE_MAP_ESCAPE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct ClosureMapEscape {
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
    explicit mylist(Mynil _v) : d_v_(_v) {}

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
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(m->v());
      return f0(d_a0, d_a1, mylist_rect<T1, T2>(f, f0, d_a1));
    }
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<mylist<T1>>, T2> F1>
  static T2 mylist_rec(const T2 f, F1 &&f0,
                       const std::shared_ptr<mylist<T1>> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(m->v());
      return f0(d_a0, d_a1, mylist_rec<T1, T2>(f, f0, d_a1));
    }
  }

  /// Build a list of closures from a list of nats using LOCAL FIXPOINTS.
  /// Each recursive call creates a fixpoint add that captures the
  /// pattern variable h from the match.
  ///
  /// BUG: Each local fixpoint uses & capture. The pattern variable h
  /// is a local binding within the match IIFE. The fixpoint is stored in
  /// mycons (a constructor), so return_captures_by_value does NOT
  /// apply. After the match, h goes out of scope, and the closure
  /// references dangling memory.
  ///
  /// Difference from fix_escape_match: uses a USER-DEFINED list type
  /// (not stdlib option), and the fixpoints are built RECURSIVELY
  /// from list elements (not a single fixpoint).
  static std::shared_ptr<mylist<std::function<unsigned int(unsigned int)>>>
  map_to_adders(const std::shared_ptr<mylist<unsigned int>> &l);
  __attribute__((pure)) static unsigned int apply_first(
      const std::shared_ptr<mylist<std::function<unsigned int(unsigned int)>>>
          &fns,
      const unsigned int arg);
  __attribute__((pure)) static unsigned int sum_apply(
      const std::shared_ptr<mylist<std::function<unsigned int(unsigned int)>>>
          &fns,
      const unsigned int
          arg); /// test1: map_to_adders 10, 20, 30, apply first to 5.
  /// add(5) where add(x) = x + 10. So 10 + 5 = 15.
  /// Bug: h=10 captured by &, dangling after match.
  static inline const unsigned int test1 =
      apply_first(map_to_adders(mylist<unsigned int>::mycons(
                      10u, mylist<unsigned int>::mycons(
                               20u, mylist<unsigned int>::mycons(
                                        30u, mylist<unsigned int>::mynil())))),
                  5u);
  /// test2: Sum of applying all adders to 0.
  /// (0+10) + (0+20) + (0+30) = 60.
  static inline const unsigned int test2 =
      sum_apply(map_to_adders(mylist<unsigned int>::mycons(
                    10u, mylist<unsigned int>::mycons(
                             20u, mylist<unsigned int>::mycons(
                                      30u, mylist<unsigned int>::mynil())))),
                0u);
  /// test3: Build adders, noise, then apply.
  /// (1+100) + (1+200) = 302.
  static inline const unsigned int test3 = []() {
    std::shared_ptr<mylist<std::function<unsigned int(unsigned int)>>> fns =
        map_to_adders(mylist<unsigned int>::mycons(
            100u,
            mylist<unsigned int>::mycons(200u, mylist<unsigned int>::mynil())));
    return sum_apply(std::move(fns), 1u);
  }();
};

#endif // INCLUDED_CLOSURE_MAP_ESCAPE
