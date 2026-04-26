#ifndef INCLUDED_MUTUAL_RECORD
#define INCLUDED_MUTUAL_RECORD

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

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{clone_value(d_a0), clone_value(d_a1)});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{clone_as_value<t_A>(d_a0),
                  d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

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
      List<std::unique_ptr<employee>> d_a1;
    };

    using variant_t = std::variant<Mk_department>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    department() {}

    explicit department(Mk_department _v) : d_v_(std::move(_v)) {}

    department(const department &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    department(department &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) department &operator=(const department &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) department &operator=(department &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) department clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Mk_department>(_sv.v());
      return department(Mk_department{
          d_a0,
          clone_as_value<List<std::unique_ptr<MutualRecord::employee>>>(d_a1)});
    }

    // CREATORS
    __attribute__((pure)) static department mk_department(unsigned int a0,
                                                          List<employee> a1) {
      return department(Mk_department{
          std::move(a0),
          clone_as_value<List<std::unique_ptr<MutualRecord::employee>>>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) department *operator->() { return this; }

    __attribute__((pure)) const department *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = department(); }

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
    employee() {}

    explicit employee(Mk_employee _v) : d_v_(std::move(_v)) {}

    employee(const employee &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    employee(employee &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) employee &operator=(const employee &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) employee &operator=(employee &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) employee clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Mk_employee>(_sv.v());
      return employee(Mk_employee{d_a0, d_a1});
    }

    // CREATORS
    __attribute__((pure)) static employee mk_employee(unsigned int a0,
                                                      unsigned int a1) {
      return employee(Mk_employee{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) employee *operator->() { return this; }

    __attribute__((pure)) const employee *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = employee(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, List<employee>> F0>
  static T1 department_rect(F0 &&f, const department &d) {
    const auto &[d_a0, d_a1] =
        std::get<typename department::Mk_department>(d.v());
    return f(d_a0, clone_as_value<List<MutualRecord::employee>>(d_a1));
  }

  template <typename T1, MapsTo<T1, unsigned int, List<employee>> F0>
  static T1 department_rec(F0 &&f, const department &d) {
    const auto &[d_a0, d_a1] =
        std::get<typename department::Mk_department>(d.v());
    return f(d_a0, clone_as_value<List<MutualRecord::employee>>(d_a1));
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 employee_rect(F0 &&f, const employee &e) {
    const auto &[d_a0, d_a1] = std::get<typename employee::Mk_employee>(e.v());
    return f(d_a0, d_a1);
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 employee_rec(F0 &&f, const employee &e) {
    const auto &[d_a0, d_a1] = std::get<typename employee::Mk_employee>(e.v());
    return f(d_a0, d_a1);
  }

  __attribute__((pure)) static unsigned int dept_id(const department &d);
  __attribute__((pure)) static List<employee>
  dept_employees(const department &d);
  __attribute__((pure)) static unsigned int emp_id(const employee &e);
  __attribute__((pure)) static unsigned int emp_salary(const employee &e);
  __attribute__((pure)) static unsigned int
  dept_total_salary(const department &d);
  __attribute__((pure)) static unsigned int
  emp_list_salary(const List<employee> &l);
  __attribute__((pure)) static unsigned int dept_count(const department &d);
  __attribute__((pure)) static unsigned int
  emp_list_count(const List<employee> &l);
  static inline const employee emp1 = employee::mk_employee(1u, 50u);
  static inline const employee emp2 = employee::mk_employee(2u, 60u);
  static inline const employee emp3 = employee::mk_employee(3u, 70u);
  static inline const department test_dept = department::mk_department(
      100u,
      List<employee>::cons(
          emp1, List<employee>::cons(
                    emp2, List<employee>::cons(emp3, List<employee>::nil()))));
  static inline const unsigned int test_total_salary =
      dept_total_salary(test_dept);
  static inline const unsigned int test_dept_count = dept_count(test_dept);
  static inline const unsigned int test_dept_id = dept_id(test_dept);
};

#endif // INCLUDED_MUTUAL_RECORD
