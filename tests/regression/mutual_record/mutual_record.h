#ifndef INCLUDED_MUTUAL_RECORD
#define INCLUDED_MUTUAL_RECORD

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

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
  static T1 department_rect(F0 &&f, const department &d) {
    const auto &[a0, a1] = std::get<typename department::Mk_department>(d.v());
    return f(a0, *a1);
  }

  template <typename T1, typename F0>
  static T1 department_rec(F0 &&f, const department &d) {
    return department_rect<T1>(f, d);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &, const uint64_t &>
  static T1 employee_rect(F0 &&f, const employee &e) {
    const auto &[a0, a1] = std::get<typename employee::Mk_employee>(e.v());
    return f(a0, a1);
  }

  template <typename T1, typename F0>
  static T1 employee_rec(F0 &&f, const employee &e) {
    return employee_rect<T1>(f, e);
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
  static constexpr uint64_t test_total_salary = UINT64_C(180);
  static constexpr uint64_t test_dept_count = UINT64_C(3);
  static constexpr uint64_t test_dept_id = UINT64_C(100);
};

#endif // INCLUDED_MUTUAL_RECORD
