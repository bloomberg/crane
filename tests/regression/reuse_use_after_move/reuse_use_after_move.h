#ifndef INCLUDED_REUSE_USE_AFTER_MOVE
#define INCLUDED_REUSE_USE_AFTER_MOVE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

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
      std::unique_ptr<mylist> d_a1;
    };

    struct Mynil {};

    using variant_t = std::variant<Mycons, Mynil>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

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
      if (std::holds_alternative<Mycons>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<Mycons>(_sv.v());
        return mylist(
            Mycons{d_a0, clone_as_value<std::unique_ptr<mylist>>(d_a1)});
      } else {
        return mylist(Mynil{});
      }
    }

    // CREATORS
    __attribute__((pure)) static mylist mycons(unsigned int a0,
                                               const mylist &a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist>(a1.clone())});
    }

    __attribute__((pure)) static mylist mynil() { return mylist(Mynil{}); }

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

  template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F0>
  static T1 mylist_rect(F0 &&f, const T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(m.v());
      return f(d_a0, *(d_a1), mylist_rect<T1>(f, f0, *(d_a1)));
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F0>
  static T1 mylist_rec(F0 &&f, const T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(m.v());
      return f(d_a0, *(d_a1), mylist_rec<T1>(f, f0, *(d_a1)));
    } else {
      return f0;
    }
  }

  __attribute__((pure)) static unsigned int length(const mylist &l);
  __attribute__((pure)) static unsigned int sum(const mylist &l);
  /// BUG: The reuse optimization fires because:
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
  __attribute__((pure)) static mylist rewrite_head(mylist l, const bool &b);
  /// test1: rewrite_head on 1, 2, 3 with true.
  /// Expected: length 1,2,3 = 3, so result = 3, 2, 3.
  /// Bug: null dereference inside length.
  static inline const unsigned int test1 = []() {
    auto &&_sv0 = rewrite_head(
        mylist::mycons(1u,
                       mylist::mycons(2u, mylist::mycons(3u, mylist::mynil()))),
        true);
    if (std::holds_alternative<typename mylist::Mycons>(_sv0.v())) {
      const auto &[d_a00, d_a10] = std::get<typename mylist::Mycons>(_sv0.v());
      return d_a00;
    } else {
      return 999u;
    }
  }();
  /// test2: Use sum instead of length — same bug pattern.
  __attribute__((pure)) static mylist rewrite_head_sum(mylist l, const bool &b);
  static inline const unsigned int test2 = []() {
    auto &&_sv0 = rewrite_head_sum(
        mylist::mycons(
            10u, mylist::mycons(20u, mylist::mycons(30u, mylist::mynil()))),
        true);
    if (std::holds_alternative<typename mylist::Mycons>(_sv0.v())) {
      const auto &[d_a00, d_a10] = std::get<typename mylist::Mycons>(_sv0.v());
      return d_a00;
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_REUSE_USE_AFTER_MOVE
