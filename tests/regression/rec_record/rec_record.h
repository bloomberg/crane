#ifndef INCLUDED_REC_RECORD
#define INCLUDED_REC_RECORD

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

struct RecRecord {
  template <typename A> struct rlist {
    // TYPES
    struct Rnil {};

    struct Rcons {
      A a0;
      std::shared_ptr<rlist<A>> a1;
    };

    using variant_t = std::variant<Rnil, Rcons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rlist() {}

    explicit rlist(Rnil _v) : v_(_v) {}

    explicit rlist(Rcons _v) : v_(std::move(_v)) {}

    template <typename _U> explicit rlist(const rlist<_U> &_other) {
      if (std::holds_alternative<typename rlist<_U>::Rnil>(_other.v())) {
        this->v_ = Rnil{};
      } else {
        const auto &[a0, a1] = std::get<typename rlist<_U>::Rcons>(_other.v());
        this->v_ = Rcons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<rlist<A>>(*a1) : nullptr};
      }
    }

    static rlist<A> rnil() { return rlist(Rnil{}); }

    static rlist<A> rcons(A a0, rlist<A> a1) {
      return rlist(
          Rcons{std::move(a0), std::make_shared<rlist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, rlist<T1> &, T2 &>
  static T2 rlist_rect(T2 f, F1 &&f0, const rlist<T1> &r) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(r.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename rlist<T1>::Rcons>(r.v());
      return f0(a0, *a1, rlist_rect<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, rlist<T1> &, T2 &>
  static T2 rlist_rec(T2 f, F1 &&f0, const rlist<T1> &r) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(r.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename rlist<T1>::Rcons>(r.v());
      return f0(a0, *a1, rlist_rec<T1, T2>(f, f0, *a1));
    }
  }

  struct RNode {
    uint64_t rn_value;
    std::optional<std::shared_ptr<RNode>> rn_next;
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, std::optional<RNode> &>
  static T1 RNode_rect(F0 &&f, const RNode &r) {
    uint64_t rn_value0 = r.rn_value;
    std::optional<RNode> rn_next0{};
    const auto &__cv = r.rn_next;
    if (__cv.has_value()) {
      const std::shared_ptr<RNode> &_cv0_0 = *__cv;
      rn_next0 = std::make_optional<RNode>((*_cv0_0));
    } else {
      rn_next0 = std::optional<RNode>();
    }
    return f(rn_value0, rn_next0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, std::optional<RNode> &>
  static T1 RNode_rec(F0 &&f, const RNode &r) {
    uint64_t rn_value0 = r.rn_value;
    std::optional<RNode> rn_next0{};
    const auto &__cv = r.rn_next;
    if (__cv.has_value()) {
      const std::shared_ptr<RNode> &_cv0_0 = *__cv;
      rn_next0 = std::make_optional<RNode>((*_cv0_0));
    } else {
      rn_next0 = std::optional<RNode>();
    }
    return f(rn_value0, rn_next0);
  }

  struct Employee {
    uint64_t emp_name;
    uint64_t emp_dept;
  };

  struct Department {
    uint64_t dept_id;
    Employee dept_head;
    uint64_t dept_size;
  };

  template <typename T1> static uint64_t rlist_length(const rlist<T1> &l) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename rlist<T1>::Rcons>(l.v());
      return (rlist_length<T1>(*a1) + 1);
    }
  }

  static uint64_t rlist_sum(const rlist<uint64_t> &l);
  static uint64_t rnode_depth(const RNode &r);
  static inline const rlist<uint64_t> test_rlist = rlist<uint64_t>::rcons(
      UINT64_C(1), rlist<uint64_t>::rcons(
                       UINT64_C(2), rlist<uint64_t>::rcons(
                                        UINT64_C(3), rlist<uint64_t>::rnil())));
  static inline const uint64_t test_rlist_len =
      rlist_length<uint64_t>(test_rlist);
  static inline const uint64_t test_rlist_sum = rlist_sum(test_rlist);
  static inline const RNode test_rnode = RNode{
      UINT64_C(1),
      [](const auto &__cv)
          -> std::optional<std::shared_ptr<RNode>> {
        if (__cv.has_value()) {
          const RNode &_cv0_0 = *__cv;
          return std::make_optional<std::shared_ptr<RNode>>(
              std::make_shared<RNode>(_cv0_0));
        } else {
          return std::optional<std::shared_ptr<RNode>>();
        }
      }(std::make_optional<RNode>(RNode{
              UINT64_C(2),
              [](const auto &__cv)
                  -> std::optional<std::shared_ptr<RNode>> {
                if (__cv.has_value()) {
                  const RNode &_cv0_0 = *__cv;
                  return std::make_optional<std::shared_ptr<RNode>>(
                      std::make_shared<RNode>(_cv0_0));
                } else {
                  return std::optional<std::shared_ptr<RNode>>();
                }
              }(std::make_optional<RNode>(RNode{
                      UINT64_C(3),
                      [](const auto &__cv)
                          -> std::optional<std::shared_ptr<RNode>> {
                        if (__cv.has_value()) {
                          const RNode &_cv0_0 = *__cv;
                          return std::make_optional<std::shared_ptr<RNode>>(
                              std::make_shared<RNode>(_cv0_0));
                        } else {
                          return std::optional<std::shared_ptr<RNode>>();
                        }
                      }(std::optional<RNode>())}))}))};
  static inline const uint64_t test_rnode_depth = rnode_depth(test_rnode);
  static inline const Employee test_emp = Employee{UINT64_C(42), UINT64_C(7)};
  static inline const Department test_dept =
      Department{UINT64_C(7), test_emp, UINT64_C(50)};
  static inline const uint64_t test_dept_head_name =
      test_dept.dept_head.emp_name;
};

#endif // INCLUDED_REC_RECORD
