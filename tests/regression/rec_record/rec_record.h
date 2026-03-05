#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct RecRecord {
  template <typename A> struct rlist {
  public:
    struct rnil {};
    struct rcons {
      A _a0;
      std::shared_ptr<rlist<A>> _a1;
    };
    using variant_t = std::variant<rnil, rcons>;

  private:
    variant_t v_;
    explicit rlist(rnil _v) : v_(std::move(_v)) {}
    explicit rlist(rcons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<rlist<A>> rnil_() {
        return std::shared_ptr<rlist<A>>(new rlist<A>(rnil{}));
      }
      static std::shared_ptr<rlist<A>>
      rcons_(A a0, const std::shared_ptr<rlist<A>> &a1) {
        return std::shared_ptr<rlist<A>>(new rlist<A>(rcons{a0, a1}));
      }
      static std::unique_ptr<rlist<A>> rnil_uptr() {
        return std::unique_ptr<rlist<A>>(new rlist<A>(rnil{}));
      }
      static std::unique_ptr<rlist<A>>
      rcons_uptr(A a0, const std::shared_ptr<rlist<A>> &a1) {
        return std::unique_ptr<rlist<A>>(new rlist<A>(rcons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<rlist<T1>>, T2> F1>
  static T2 rlist_rect(const T2 f, F1 &&f0,
                       const std::shared_ptr<rlist<T1>> &r) {
    return std::visit(
        Overloaded{
            [&](const typename rlist<T1>::rnil _args) -> T2 { return f; },
            [&](const typename rlist<T1>::rcons _args) -> T2 {
              T1 y = _args._a0;
              std::shared_ptr<rlist<T1>> r0 = _args._a1;
              return f0(y, r0, rlist_rect<T1, T2>(f, f0, r0));
            }},
        r->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<rlist<T1>>, T2> F1>
  static T2 rlist_rec(const T2 f, F1 &&f0,
                      const std::shared_ptr<rlist<T1>> &r) {
    return std::visit(
        Overloaded{
            [&](const typename rlist<T1>::rnil _args) -> T2 { return f; },
            [&](const typename rlist<T1>::rcons _args) -> T2 {
              T1 y = _args._a0;
              std::shared_ptr<rlist<T1>> r0 = _args._a1;
              return f0(y, r0, rlist_rec<T1, T2>(f, f0, r0));
            }},
        r->v());
  }

  struct RNode {
    unsigned int rn_value;
    std::optional<std::shared_ptr<RNode>> rn_next;
  };

  template <typename T1,
            MapsTo<T1, unsigned int, std::optional<std::shared_ptr<RNode>>> F0>
  static T1 RNode_rect(F0 &&f, const std::shared_ptr<RNode> &r) {
    return [&](void) {
      unsigned int rn_value0 = r->rn_value;
      std::optional<std::shared_ptr<RNode>> rn_next0 = r->rn_next;
      return f(rn_value0, rn_next0);
    }();
  }

  template <typename T1,
            MapsTo<T1, unsigned int, std::optional<std::shared_ptr<RNode>>> F0>
  static T1 RNode_rec(F0 &&f, const std::shared_ptr<RNode> &r) {
    return [&](void) {
      unsigned int rn_value0 = r->rn_value;
      std::optional<std::shared_ptr<RNode>> rn_next0 = r->rn_next;
      return f(rn_value0, rn_next0);
    }();
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
  static unsigned int rlist_length(const std::shared_ptr<rlist<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename rlist<T1>::rnil _args) -> unsigned int {
                     return 0;
                   },
                   [](const typename rlist<T1>::rcons _args) -> unsigned int {
                     std::shared_ptr<rlist<T1>> rest = _args._a1;
                     return (rlist_length<T1>(std::move(rest)) + 1);
                   }},
        l->v());
  }

  static unsigned int rlist_sum(const std::shared_ptr<rlist<unsigned int>> &l);

  static unsigned int rnode_depth(const std::shared_ptr<RNode> &r);

  static inline const std::shared_ptr<rlist<unsigned int>> test_rlist =
      rlist<unsigned int>::ctor::rcons_(
          (0 + 1), rlist<unsigned int>::ctor::rcons_(
                       ((0 + 1) + 1), rlist<unsigned int>::ctor::rcons_(
                                          (((0 + 1) + 1) + 1),
                                          rlist<unsigned int>::ctor::rnil_())));

  static inline const unsigned int test_rlist_len =
      rlist_length<unsigned int>(test_rlist);

  static inline const unsigned int test_rlist_sum = rlist_sum(test_rlist);

  static inline const std::shared_ptr<RNode> test_rnode =
      std::make_shared<RNode>(RNode{
          (0 + 1),
          std::make_optional<std::shared_ptr<RNode>>(std::make_shared<RNode>(
              RNode{((0 + 1) + 1),
                    std::make_optional<std::shared_ptr<RNode>>(
                        std::make_shared<RNode>(
                            RNode{(((0 + 1) + 1) + 1), std::nullopt}))}))});

  static inline const unsigned int test_rnode_depth = rnode_depth(test_rnode);

  static inline const std::shared_ptr<Employee> test_emp =
      std::make_shared<Employee>(Employee{
          ((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) +
                                               1) +
                                              1) +
                                             1) +
                                            1) +
                                           1) +
                                          1) +
                                         1) +
                                        1) +
                                       1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1),
          (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1)});

 static inline const std::shared_ptr<Department> test_dept = std::make_shared<Department>(Department{(((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1), test_emp, ((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)});

 static inline const unsigned int test_dept_head_name =
     test_dept->dept_head->emp_name;
};
