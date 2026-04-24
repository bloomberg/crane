#ifndef INCLUDED_REC_RECORD
#define INCLUDED_REC_RECORD

#include <memory>
#include <optional>
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
  return x ? std::make_shared<T>(x->clone()) : nullptr;
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

struct RecRecord {
  template <typename t_A> struct rlist {
    // TYPES
    struct Rnil {};

    struct Rcons {
      t_A d_a0;
      std::unique_ptr<rlist<t_A>> d_a1;
    };

    using variant_t = std::variant<Rnil, Rcons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    rlist() {}

    explicit rlist(Rnil _v) : d_v_(_v) {}

    explicit rlist(Rcons _v) : d_v_(std::move(_v)) {}

    rlist(const rlist<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    rlist(rlist<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) rlist<t_A> &operator=(const rlist<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) rlist<t_A> &operator=(rlist<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) rlist<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Rnil>(_sv.v())) {
        return rlist<t_A>(Rnil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Rcons>(_sv.v());
        return rlist<t_A>(
            Rcons{clone_as_value<t_A>(d_a0),
                  clone_as_value<std::unique_ptr<rlist<t_A>>>(d_a1)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) rlist<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Rnil>(_sv.v())) {
        return rlist<_CloneT0>(typename rlist<_CloneT0>::Rnil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Rcons>(_sv.v());
        return rlist<_CloneT0>(typename rlist<_CloneT0>::Rcons{
            clone_as_value<_CloneT0>(d_a0),
            clone_as_value<std::unique_ptr<rlist<_CloneT0>>>(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static rlist<t_A> rnil() { return rlist(Rnil{}); }

    __attribute__((pure)) static rlist<t_A> rcons(t_A a0,
                                                  const rlist<t_A> &a1) {
      return rlist(
          Rcons{std::move(a0), std::make_unique<rlist<t_A>>(a1.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) rlist<t_A> *operator->() { return this; }

    __attribute__((pure)) const rlist<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = rlist<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, rlist<T1>, T2> F1>
  static T2 rlist_rect(const T2 f, F1 &&f0, const rlist<T1> &r) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(r.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename rlist<T1>::Rcons>(r.v());
      return f0(d_a0, *(d_a1), rlist_rect<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1, rlist<T1>, T2> F1>
  static T2 rlist_rec(const T2 f, F1 &&f0, const rlist<T1> &r) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(r.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename rlist<T1>::Rcons>(r.v());
      return f0(d_a0, *(d_a1), rlist_rec<T1, T2>(f, f0, *(d_a1)));
    }
  }

  struct RNode {
    unsigned int rn_value;
    std::optional<RNode> rn_next;

    __attribute__((pure)) RNode *operator->() { return this; }

    __attribute__((pure)) const RNode *operator->() const { return this; }
  };

  template <typename T1, MapsTo<T1, unsigned int, std::optional<RNode>> F0>
  static T1 RNode_rect(F0 &&f, const RNode &r) {
    unsigned int rn_value0 = r.rn_value;
    std::optional<RNode> rn_next0 = r.rn_next;
    return f(rn_value0, rn_next0);
  }

  template <typename T1, MapsTo<T1, unsigned int, std::optional<RNode>> F0>
  static T1 RNode_rec(F0 &&f, const RNode &r) {
    unsigned int rn_value0 = r.rn_value;
    std::optional<RNode> rn_next0 = r.rn_next;
    return f(rn_value0, rn_next0);
  }

  struct Employee {
    unsigned int emp_name;
    unsigned int emp_dept;

    __attribute__((pure)) Employee *operator->() { return this; }

    __attribute__((pure)) const Employee *operator->() const { return this; }
  };

  struct Department {
    unsigned int dept_id;
    Employee dept_head;
    unsigned int dept_size;

    __attribute__((pure)) Department *operator->() { return this; }

    __attribute__((pure)) const Department *operator->() const { return this; }
  };

  template <typename T1>
  __attribute__((pure)) static unsigned int rlist_length(const rlist<T1> &l) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(l.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename rlist<T1>::Rcons>(l.v());
      return (rlist_length<T1>(*(d_a1)) + 1);
    }
  }

  __attribute__((pure)) static unsigned int
  rlist_sum(const rlist<unsigned int> &l);
  __attribute__((pure)) static unsigned int rnode_depth(const RNode &r);
  static inline const rlist<unsigned int> test_rlist =
      rlist<unsigned int>::rcons(
          1u,
          rlist<unsigned int>::rcons(
              2u, rlist<unsigned int>::rcons(3u, rlist<unsigned int>::rnil())));
  static inline const unsigned int test_rlist_len =
      rlist_length<unsigned int>(test_rlist);
  static inline const unsigned int test_rlist_sum = rlist_sum(test_rlist);
  static inline const RNode test_rnode = RNode{
      1u,
      std::make_optional<RNode>(RNode{
          2u, std::make_optional<RNode>(RNode{3u, std::optional<RNode>()})})};
  static inline const unsigned int test_rnode_depth = rnode_depth(test_rnode);
  static inline const Employee test_emp = Employee{42u, 7u};
  static inline const Department test_dept = Department{7u, test_emp, 50u};
  static inline const unsigned int test_dept_head_name =
      test_dept.dept_head.emp_name;
};

#endif // INCLUDED_REC_RECORD
