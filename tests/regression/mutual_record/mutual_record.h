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

template <typename A> struct List {
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }

    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct MutualRecord {
  struct department;
  struct employee;

  struct department {
    // TYPES
    struct mk_department {
      unsigned int _a0;
      std::shared_ptr<List<std::shared_ptr<employee>>> _a1;
    };

    using variant_t = std::variant<mk_department>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit department(mk_department _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<department> mk_department_(
          unsigned int a0,
          const std::shared_ptr<List<std::shared_ptr<employee>>> &a1) {
        return std::shared_ptr<department>(
            new department(mk_department{a0, a1}));
      }

      static std::unique_ptr<department> mk_department_uptr(
          unsigned int a0,
          const std::shared_ptr<List<std::shared_ptr<employee>>> &a1) {
        return std::unique_ptr<department>(
            new department(mk_department{a0, a1}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct employee {
    // TYPES
    struct mk_employee {
      unsigned int _a0;
      unsigned int _a1;
    };

    using variant_t = std::variant<mk_employee>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit employee(mk_employee _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<employee> mk_employee_(unsigned int a0,
                                                    unsigned int a1) {
        return std::shared_ptr<employee>(new employee(mk_employee{a0, a1}));
      }

      static std::unique_ptr<employee> mk_employee_uptr(unsigned int a0,
                                                        unsigned int a1) {
        return std::unique_ptr<employee>(new employee(mk_employee{a0, a1}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <
      typename T1,
      MapsTo<T1, unsigned int, std::shared_ptr<List<std::shared_ptr<employee>>>>
          F0>
  static T1 department_rect(F0 &&f, const std::shared_ptr<department> &d) {
    return std::visit(
        Overloaded{[&](const typename department::mk_department _args) -> T1 {
          unsigned int n = _args._a0;
          std::shared_ptr<List<std::shared_ptr<employee>>> l = _args._a1;
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
        Overloaded{[&](const typename department::mk_department _args) -> T1 {
          unsigned int n = _args._a0;
          std::shared_ptr<List<std::shared_ptr<employee>>> l = _args._a1;
          return f(std::move(n), std::move(l));
        }},
        d->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 employee_rect(F0 &&f, const std::shared_ptr<employee> &e) {
    return std::visit(
        Overloaded{[&](const typename employee::mk_employee _args) -> T1 {
          unsigned int n = _args._a0;
          unsigned int n0 = _args._a1;
          return f(std::move(n), std::move(n0));
        }},
        e->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 employee_rec(F0 &&f, const std::shared_ptr<employee> &e) {
    return std::visit(
        Overloaded{[&](const typename employee::mk_employee _args) -> T1 {
          unsigned int n = _args._a0;
          unsigned int n0 = _args._a1;
          return f(std::move(n), std::move(n0));
        }},
        e->v());
  }

  static unsigned int dept_id(const std::shared_ptr<department> &d);
  static std::shared_ptr<List<std::shared_ptr<employee>>>
  dept_employees(const std::shared_ptr<department> &d);
  static unsigned int emp_id(const std::shared_ptr<employee> &e);
  static unsigned int emp_salary(const std::shared_ptr<employee> &e);
  static unsigned int dept_total_salary(const std::shared_ptr<department> &d);
  static unsigned int
  emp_list_salary(const std::shared_ptr<List<std::shared_ptr<employee>>> &l);
  static unsigned int dept_count(const std::shared_ptr<department> &d);
  static unsigned int
  emp_list_count(const std::shared_ptr<List<std::shared_ptr<employee>>> &l);
  static inline const std::shared_ptr<employee> emp1 =
      employee::ctor::mk_employee_(1u, 50u);
  static inline const std::shared_ptr<employee> emp2 =
      employee::ctor::mk_employee_(2u, 60u);
  static inline const std::shared_ptr<employee> emp3 =
      employee::ctor::mk_employee_(3u, 70u);
  static inline const std::shared_ptr<department> test_dept =
      department::ctor::mk_department_(
          100u,
          List<std::shared_ptr<employee>>::ctor::cons_(
              emp1,
              List<std::shared_ptr<employee>>::ctor::cons_(
                  emp2,
                  List<std::shared_ptr<employee>>::ctor::cons_(
                      emp3, List<std::shared_ptr<employee>>::ctor::nil_()))));
  static inline const unsigned int test_total_salary =
      dept_total_salary(test_dept);
  static inline const unsigned int test_dept_count = dept_count(test_dept);
  static inline const unsigned int test_dept_id = dept_id(test_dept);
};
