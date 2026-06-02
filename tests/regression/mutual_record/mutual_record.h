#ifndef INCLUDED_MUTUAL_RECORD
#define INCLUDED_MUTUAL_RECORD

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
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
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct MutualRecord {
  struct department;
  struct employee;

  struct department {
    // TYPES
    struct Mk_department {
      uint64_t a0;
      std::shared_ptr<List<employee>> a1;
    };

    using variant_t = std::variant<Mk_department>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    department() {}

    explicit department(Mk_department _v) : v_(std::move(_v)) {}

    static department mk_department(uint64_t a0, List<employee> a1) {
      return department(
          Mk_department{a0, std::make_shared<List<employee>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct employee {
    // TYPES
    struct Mk_employee {
      uint64_t a0;
      uint64_t a1;
    };

    using variant_t = std::variant<Mk_employee>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    employee() {}

    explicit employee(Mk_employee _v) : v_(std::move(_v)) {}

    static employee mk_employee(uint64_t a0, uint64_t a1) {
      return employee(Mk_employee{a0, a1});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<employee> &>
  static T1 department_rect(F0 &&f, const department &d) {
    const auto &[a0, a1] = std::get<typename department::Mk_department>(d.v());
    return f(a0, *a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<employee> &>
  static T1 department_rec(F0 &&f, const department &d) {
    const auto &[a0, a1] = std::get<typename department::Mk_department>(d.v());
    return f(a0, *a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &>
  static T1 employee_rect(F0 &&f, const employee &e) {
    const auto &[a0, a1] = std::get<typename employee::Mk_employee>(e.v());
    return f(a0, a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &>
  static T1 employee_rec(F0 &&f, const employee &e) {
    const auto &[a0, a1] = std::get<typename employee::Mk_employee>(e.v());
    return f(a0, a1);
  }

  static uint64_t dept_id(const department &d);
  static List<employee> dept_employees(const department &d);
  static uint64_t emp_id(const employee &e);
  static uint64_t emp_salary(const employee &e);
  static uint64_t dept_total_salary(const department &d);
  static uint64_t emp_list_salary(const List<employee> &l);
  static uint64_t dept_count(const department &d);
  static uint64_t emp_list_count(const List<employee> &l);
  static inline const employee emp1 =
      employee::mk_employee(UINT64_C(1), UINT64_C(50));
  static inline const employee emp2 =
      employee::mk_employee(UINT64_C(2), UINT64_C(60));
  static inline const employee emp3 =
      employee::mk_employee(UINT64_C(3), UINT64_C(70));
  static inline const department test_dept = department::mk_department(
      UINT64_C(100),
      List<employee>::cons(
          emp1, List<employee>::cons(
                    emp2, List<employee>::cons(emp3, List<employee>::nil()))));
  static inline const uint64_t test_total_salary = dept_total_salary(test_dept);
  static inline const uint64_t test_dept_count = dept_count(test_dept);
  static inline const uint64_t test_dept_id = dept_id(test_dept);
};

#endif // INCLUDED_MUTUAL_RECORD
