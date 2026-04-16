#ifndef INCLUDED_MUTUAL_RECORD
#define INCLUDED_MUTUAL_RECORD

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

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

  public:
    // CREATORS
    explicit department(Mk_department _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<department>
    mk_department(unsigned int a0,
                  const std::shared_ptr<List<std::shared_ptr<employee>>> &a1) {
      return std::make_shared<department>(Mk_department{std::move(a0), a1});
    }

    static std::shared_ptr<department>
    mk_department(unsigned int a0,
                  std::shared_ptr<List<std::shared_ptr<employee>>> &&a1) {
      return std::make_shared<department>(
          Mk_department{std::move(a0), std::move(a1)});
    }

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

  public:
    // CREATORS
    explicit employee(Mk_employee _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<employee> mk_employee(unsigned int a0,
                                                 unsigned int a1) {
      return std::make_shared<employee>(
          Mk_employee{std::move(a0), std::move(a1)});
    }

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
    const auto &[d_a0, d_a1] =
        std::get<typename department::Mk_department>(d->v());
    return f(d_a0, d_a1);
  }

  template <
      typename T1,
      MapsTo<T1, unsigned int, std::shared_ptr<List<std::shared_ptr<employee>>>>
          F0>
  static T1 department_rec(F0 &&f, const std::shared_ptr<department> &d) {
    const auto &[d_a0, d_a1] =
        std::get<typename department::Mk_department>(d->v());
    return f(d_a0, d_a1);
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 employee_rect(F0 &&f, const std::shared_ptr<employee> &e) {
    const auto &[d_a0, d_a1] = std::get<typename employee::Mk_employee>(e->v());
    return f(d_a0, d_a1);
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 employee_rec(F0 &&f, const std::shared_ptr<employee> &e) {
    const auto &[d_a0, d_a1] = std::get<typename employee::Mk_employee>(e->v());
    return f(d_a0, d_a1);
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
      employee::mk_employee(1u, 50u);
  static inline const std::shared_ptr<employee> emp2 =
      employee::mk_employee(2u, 60u);
  static inline const std::shared_ptr<employee> emp3 =
      employee::mk_employee(3u, 70u);
  static inline const std::shared_ptr<department> test_dept =
      department::mk_department(
          100u,
          List<std::shared_ptr<employee>>::cons(
              emp1,
              List<std::shared_ptr<employee>>::cons(
                  emp2, List<std::shared_ptr<employee>>::cons(
                            emp3, List<std::shared_ptr<employee>>::nil()))));
  static inline const unsigned int test_total_salary =
      dept_total_salary(test_dept);
  static inline const unsigned int test_dept_count = dept_count(test_dept);
  static inline const unsigned int test_dept_id = dept_id(test_dept);
};

#endif // INCLUDED_MUTUAL_RECORD
