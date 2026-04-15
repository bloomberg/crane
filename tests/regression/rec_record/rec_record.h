#ifndef INCLUDED_REC_RECORD
#define INCLUDED_REC_RECORD

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct RecRecord {
  template <typename t_A> struct rlist {
    // TYPES
    struct Rnil {};

    struct Rcons {
      t_A d_a0;
      std::shared_ptr<rlist<t_A>> d_a1;
    };

    using variant_t = std::variant<Rnil, Rcons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit rlist(Rnil _v) : d_v_(_v) {}

    explicit rlist(Rcons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<rlist<t_A>> rnil() {
      return std::make_shared<rlist<t_A>>(Rnil{});
    }

    static std::shared_ptr<rlist<t_A>>
    rcons(t_A a0, const std::shared_ptr<rlist<t_A>> &a1) {
      return std::make_shared<rlist<t_A>>(Rcons{std::move(a0), a1});
    }

    static std::shared_ptr<rlist<t_A>> rcons(t_A a0,
                                             std::shared_ptr<rlist<t_A>> &&a1) {
      return std::make_shared<rlist<t_A>>(Rcons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<rlist<T1>>, T2> F1>
  static T2 rlist_rect(const T2 f, F1 &&f0,
                       const std::shared_ptr<rlist<T1>> &r) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(r->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename rlist<T1>::Rcons>(r->v());
      return f0(d_a0, d_a1, rlist_rect<T1, T2>(f, f0, d_a1));
    }
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<rlist<T1>>, T2> F1>
  static T2 rlist_rec(const T2 f, F1 &&f0,
                      const std::shared_ptr<rlist<T1>> &r) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(r->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename rlist<T1>::Rcons>(r->v());
      return f0(d_a0, d_a1, rlist_rec<T1, T2>(f, f0, d_a1));
    }
  }

  struct RNode {
    unsigned int rn_value;
    std::optional<std::shared_ptr<RNode>> rn_next;
  };

  template <typename T1,
            MapsTo<T1, unsigned int, std::optional<std::shared_ptr<RNode>>> F0>
  static T1 RNode_rect(F0 &&f, const std::shared_ptr<RNode> &r) {
    unsigned int rn_value0 = r->rn_value;
    std::optional<std::shared_ptr<RNode>> rn_next0 = r->rn_next;
    return f(rn_value0, rn_next0);
  }

  template <typename T1,
            MapsTo<T1, unsigned int, std::optional<std::shared_ptr<RNode>>> F0>
  static T1 RNode_rec(F0 &&f, const std::shared_ptr<RNode> &r) {
    unsigned int rn_value0 = r->rn_value;
    std::optional<std::shared_ptr<RNode>> rn_next0 = r->rn_next;
    return f(rn_value0, rn_next0);
  }

  struct Employee {
    unsigned int emp_name;
    unsigned int emp_dept;
  };

  struct Department {
    unsigned int dept_id;
    std::shared_ptr<Employee> dept_head;
    unsigned int dept_size;
  };

  template <typename T1>
  __attribute__((pure)) static unsigned int
  rlist_length(const std::shared_ptr<rlist<T1>> &l) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(l->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename rlist<T1>::Rcons>(l->v());
      return (rlist_length<T1>(d_a1) + 1);
    }
  }

  __attribute__((pure)) static unsigned int
  rlist_sum(const std::shared_ptr<rlist<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  rnode_depth(const std::shared_ptr<RNode> &r);
  static inline const std::shared_ptr<rlist<unsigned int>> test_rlist =
      rlist<unsigned int>::rcons(
          1u,
          rlist<unsigned int>::rcons(
              2u, rlist<unsigned int>::rcons(3u, rlist<unsigned int>::rnil())));
  static inline const unsigned int test_rlist_len =
      rlist_length<unsigned int>(test_rlist);
  static inline const unsigned int test_rlist_sum = rlist_sum(test_rlist);
  static inline const std::shared_ptr<RNode> test_rnode =
      std::make_shared<RNode>(RNode{
          1u,
          std::make_optional<std::shared_ptr<RNode>>(std::make_shared<RNode>(
              RNode{2u,
                    std::make_optional<std::shared_ptr<RNode>>(
                        std::make_shared<RNode>(RNode{
                            3u, std::optional<std::shared_ptr<RNode>>()}))}))});
  static inline const unsigned int test_rnode_depth = rnode_depth(test_rnode);
  static inline const std::shared_ptr<Employee> test_emp =
      std::make_shared<Employee>(Employee{42u, 7u});
  static inline const std::shared_ptr<Department> test_dept =
      std::make_shared<Department>(Department{7u, test_emp, 50u});
  static inline const unsigned int test_dept_head_name =
      test_dept->dept_head->emp_name;
};

#endif // INCLUDED_REC_RECORD
