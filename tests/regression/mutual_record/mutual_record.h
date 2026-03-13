#ifndef INCLUDED_MUTUAL_RECORD
#define INCLUDED_MUTUAL_RECORD

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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct MutualRecord {
  struct department;
  struct employee;

  struct department {
    // TYPES
    struct Mk_department {
      unsigned int d_a0;
      std::shared_ptr<List<std::shared_ptr<employee>>> d_a1;
    };

    using variant_t = std::variant<Mk_department>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit department(Mk_department _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<department> Mk_department_(
          unsigned int a0,
          const std::shared_ptr<List<std::shared_ptr<employee>>> &a1) {
        return std::shared_ptr<department>(
            new department(Mk_department{a0, a1}));
      }

      static std::unique_ptr<department> Mk_department_uptr(
          unsigned int a0,
          const std::shared_ptr<List<std::shared_ptr<employee>>> &a1) {
        return std::unique_ptr<department>(
            new department(Mk_department{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct employee {
    // TYPES
    struct Mk_employee {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    using variant_t = std::variant<Mk_employee>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit employee(Mk_employee _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<employee> Mk_employee_(unsigned int a0,
                                                    unsigned int a1) {
        return std::shared_ptr<employee>(new employee(Mk_employee{a0, a1}));
      }

      static std::unique_ptr<employee> Mk_employee_uptr(unsigned int a0,
                                                        unsigned int a1) {
        return std::unique_ptr<employee>(new employee(Mk_employee{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1,
      MapsTo<T1, unsigned int, std::shared_ptr<List<std::shared_ptr<employee>>>>
          F0>
  static T1 department_rect(F0 &&f, const std::shared_ptr<department> &d) {
    return std::visit(
        Overloaded{[&](const typename department::Mk_department _args) -> T1 {
          unsigned int n = _args.d_a0;
          std::shared_ptr<List<std::shared_ptr<employee>>> l = _args.d_a1;
          return f(std::move(n), std::move(l));
        }},
        d->v());
  }

  template <
      typename T1,
      MapsTo<T1, unsigned int, std::shared_ptr<List<std::shared_ptr<employee>>>>
          F0>
  static T1 department_rec(F0 &&f, const std::shared_ptr<department> &d) {
    return std::visit(
        Overloaded{[&](const typename department::Mk_department _args) -> T1 {
          unsigned int n = _args.d_a0;
          std::shared_ptr<List<std::shared_ptr<employee>>> l = _args.d_a1;
          return f(std::move(n), std::move(l));
        }},
        d->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 employee_rect(F0 &&f, const std::shared_ptr<employee> &e) {
    return std::visit(
        Overloaded{[&](const typename employee::Mk_employee _args) -> T1 {
          unsigned int n = _args.d_a0;
          unsigned int n0 = _args.d_a1;
          return f(std::move(n), std::move(n0));
        }},
        e->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 employee_rec(F0 &&f, const std::shared_ptr<employee> &e) {
    return std::visit(
        Overloaded{[&](const typename employee::Mk_employee _args) -> T1 {
          unsigned int n = _args.d_a0;
          unsigned int n0 = _args.d_a1;
          return f(std::move(n), std::move(n0));
        }},
        e->v());
  }

  __attribute__((pure)) static unsigned int
  dept_id(const std::shared_ptr<department> &d);
  static std::shared_ptr<List<std::shared_ptr<employee>>>
  dept_employees(const std::shared_ptr<department> &d);
  __attribute__((pure)) static unsigned int
  emp_id(const std::shared_ptr<employee> &e);
  __attribute__((pure)) static unsigned int
  emp_salary(const std::shared_ptr<employee> &e);
  __attribute__((pure)) static unsigned int
  dept_total_salary(const std::shared_ptr<department> &d);
  __attribute__((pure)) static unsigned int
  emp_list_salary(const std::shared_ptr<List<std::shared_ptr<employee>>> &l);
  __attribute__((pure)) static unsigned int
  dept_count(const std::shared_ptr<department> &d);
  __attribute__((pure)) static unsigned int
  emp_list_count(const std::shared_ptr<List<std::shared_ptr<employee>>> &l);
  static inline const std::shared_ptr<employee> emp1 =
      employee::ctor::Mk_employee_(1u, 50u);
  static inline const std::shared_ptr<employee> emp2 =
      employee::ctor::Mk_employee_(2u, 60u);
  static inline const std::shared_ptr<employee> emp3 =
      employee::ctor::Mk_employee_(3u, 70u);
  static inline const std::shared_ptr<department> test_dept =
      department::ctor::Mk_department_(
          100u,
          List<std::shared_ptr<employee>>::ctor::Cons_(
              emp1,
              List<std::shared_ptr<employee>>::ctor::Cons_(
                  emp2,
                  List<std::shared_ptr<employee>>::ctor::Cons_(
                      emp3, List<std::shared_ptr<employee>>::ctor::Nil_()))));
  static inline const unsigned int test_total_salary =
      dept_total_salary(test_dept);
  static inline const unsigned int test_dept_count = dept_count(test_dept);
  static inline const unsigned int test_dept_id = dept_id(test_dept);
};

#endif // INCLUDED_MUTUAL_RECORD
