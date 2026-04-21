#ifndef INCLUDED_REUSE_USE_AFTER_MOVE
#define INCLUDED_REUSE_USE_AFTER_MOVE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct ReuseUseAfterMove {
  /// Define mycons FIRST so it gets variant index 0.
  /// This is critical: the reuse optimization picks List.hd reuse_candidates,
  /// i.e. the first constructor branch with a matching tail constructor.
  /// By putting mycons at index 0, the reuse optimization fires on the
  /// mycons branch instead of skipping to the no-op mynil branch.
  struct mylist {
    // TYPES
    struct Mycons {
      unsigned int d_a0;
      std::shared_ptr<mylist> d_a1;
    };

    struct Mynil {};

    using variant_t = std::variant<Mycons, Mynil>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

    static std::shared_ptr<mylist> mycons(unsigned int a0,
                                          const std::shared_ptr<mylist> &a1) {
      return std::make_shared<mylist>(Mycons{std::move(a0), a1});
    }

    static std::shared_ptr<mylist> mycons(unsigned int a0,
                                          std::shared_ptr<mylist> &&a1) {
      return std::make_shared<mylist>(Mycons{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<mylist> mynil() {
      return std::make_shared<mylist>(Mynil{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1,
            MapsTo<T1, unsigned int, std::shared_ptr<mylist>, T1> F0>
  static T1 mylist_rect(F0 &&f, const T1 f0, const std::shared_ptr<mylist> &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m->v())) {
      const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(m->v());
      return f(d_a0, d_a1, mylist_rect<T1>(f, f0, d_a1));
    } else {
      return f0;
    }
  }

  template <typename T1,
            MapsTo<T1, unsigned int, std::shared_ptr<mylist>, T1> F0>
  static T1 mylist_rec(F0 &&f, const T1 f0, const std::shared_ptr<mylist> &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m->v())) {
      const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(m->v());
      return f(d_a0, d_a1, mylist_rec<T1>(f, f0, d_a1));
    } else {
      return f0;
    }
  }

  __attribute__((pure)) static unsigned int
  length(const std::shared_ptr<mylist> &l);
  __attribute__((pure)) static unsigned int
  sum(const std::shared_ptr<mylist>
          &l); /// BUG: The reuse optimization fires because:
  /// 1. l escapes in the else branch (returned in tail position)
  /// -> infer_owned_params marks l as owned (pass by value)
  /// 2. The mycons branch has tail constructor mycons with arity 2 = 2
  /// -> find_reuse_candidates finds it as a candidate
  /// 3. mycons is at index 0 -> List.hd picks it
  /// 4. At runtime, use_count() == 1 holds for fresh values
  ///
  /// The reuse branch does:
  /// auto x  = std::move(_rf.d_a0);   // unsigned int, trivial
  /// auto xs = std::move(_rf.d_a1);   // shared_ptr -> NULL
  /// _rf.d_a0 = length(l);            // length accesses l.d_a1 which is NULL!
  /// _rf.d_a1 = xs;                   // restore xs
  /// return l;
  ///
  /// length(l) traverses l, hitting the null d_a1 field.
  /// Dereferencing null shared_ptr -> CRASH.
  static std::shared_ptr<mylist> rewrite_head(std::shared_ptr<mylist> l,
                                              const bool b);
  /// test1: rewrite_head on 1, 2, 3 with true.
  /// Expected: length 1,2,3 = 3, so result = 3, 2, 3.
  /// Bug: null dereference inside length.
  static inline const unsigned int test1 = []() {
    auto &&_sv0 = rewrite_head(
        mylist::mycons(1u,
                       mylist::mycons(2u, mylist::mycons(3u, mylist::mynil()))),
        true);
    if (std::holds_alternative<typename mylist::Mycons>(_sv0->v())) {
      const auto &[d_a00, d_a10] = std::get<typename mylist::Mycons>(_sv0->v());
      return d_a00;
    } else {
      return 999u;
    }
  }();
  /// test2: Use sum instead of length — same bug pattern.
  static std::shared_ptr<mylist> rewrite_head_sum(std::shared_ptr<mylist> l,
                                                  const bool b);
  static inline const unsigned int test2 = []() {
    auto &&_sv0 = rewrite_head_sum(
        mylist::mycons(
            10u, mylist::mycons(20u, mylist::mycons(30u, mylist::mynil()))),
        true);
    if (std::holds_alternative<typename mylist::Mycons>(_sv0->v())) {
      const auto &[d_a00, d_a10] = std::get<typename mylist::Mycons>(_sv0->v());
      return d_a00;
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_REUSE_USE_AFTER_MOVE
