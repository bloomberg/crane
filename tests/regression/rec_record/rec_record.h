#ifndef INCLUDED_REC_RECORD
#define INCLUDED_REC_RECORD

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

    // CREATORS
    explicit rlist(Rnil _v) : d_v_(std::move(_v)) {}

    explicit rlist(Rcons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<rlist<t_A>> Rnil_() {
        return std::shared_ptr<rlist<t_A>>(new rlist<t_A>(Rnil{}));
      }

      static std::shared_ptr<rlist<t_A>>
      Rcons_(t_A a0, const std::shared_ptr<rlist<t_A>> &a1) {
        return std::shared_ptr<rlist<t_A>>(new rlist<t_A>(Rcons{a0, a1}));
      }

      static std::unique_ptr<rlist<t_A>> Rnil_uptr() {
        return std::unique_ptr<rlist<t_A>>(new rlist<t_A>(Rnil{}));
      }

      static std::unique_ptr<rlist<t_A>>
      Rcons_uptr(t_A a0, const std::shared_ptr<rlist<t_A>> &a1) {
        return std::unique_ptr<rlist<t_A>>(new rlist<t_A>(Rcons{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<rlist<T1>>, T2> F1>
  static T2 rlist_rect(const T2 f, F1 &&f0,
                       const std::shared_ptr<rlist<T1>> &r) {
    return std::visit(
        Overloaded{
            [&](const typename rlist<T1>::Rnil _args) -> T2 { return f; },
            [&](const typename rlist<T1>::Rcons _args) -> T2 {
              T1 y = _args.d_a0;
              std::shared_ptr<rlist<T1>> r0 = _args.d_a1;
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
            [&](const typename rlist<T1>::Rnil _args) -> T2 { return f; },
            [&](const typename rlist<T1>::Rcons _args) -> T2 {
              T1 y = _args.d_a0;
              std::shared_ptr<rlist<T1>> r0 = _args.d_a1;
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
  __attribute__((pure)) static unsigned int
  rlist_length(const std::shared_ptr<rlist<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename rlist<T1>::Rnil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename rlist<T1>::Rcons _args) -> unsigned int {
                     std::shared_ptr<rlist<T1>> rest = _args.d_a1;
                     return (rlist_length<T1>(std::move(rest)) + 1);
                   }},
        l->v());
  }

  __attribute__((pure)) static unsigned int
  rlist_sum(const std::shared_ptr<rlist<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  rnode_depth(const std::shared_ptr<RNode> &r);
  static inline const std::shared_ptr<rlist<unsigned int>> test_rlist =
      rlist<unsigned int>::ctor::Rcons_(
          1u, rlist<unsigned int>::ctor::Rcons_(
                  2u, rlist<unsigned int>::ctor::Rcons_(
                          3u, rlist<unsigned int>::ctor::Rnil_())));
  static inline const unsigned int test_rlist_len =
      rlist_length<unsigned int>(test_rlist);
  static inline const unsigned int test_rlist_sum = rlist_sum(test_rlist);
  static inline const std::shared_ptr<RNode> test_rnode =
      std::make_shared<RNode>(RNode{
          1u,
          std::make_optional<std::shared_ptr<RNode>>(std::make_shared<RNode>(
              RNode{2u,
                    std::make_optional<std::shared_ptr<RNode>>(
                        std::make_shared<RNode>(RNode{3u, std::nullopt}))}))});
  static inline const unsigned int test_rnode_depth = rnode_depth(test_rnode);
  static inline const std::shared_ptr<Employee> test_emp =
      std::make_shared<Employee>(Employee{42u, 7u});
  static inline const std::shared_ptr<Department> test_dept =
      std::make_shared<Department>(Department{7u, test_emp, 50u});
  static inline const unsigned int test_dept_head_name =
      test_dept->dept_head->emp_name;
};

#endif // INCLUDED_REC_RECORD
