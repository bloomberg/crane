#ifndef INCLUDED_MUTUAL_RECORD
#define INCLUDED_MUTUAL_RECORD

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

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
      unsigned int a0;
      std::unique_ptr<List<employee>> a1;
    };

    using variant_t = std::variant<Mk_department>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    department() {}

    explicit department(Mk_department _v) : v_(std::move(_v)) {}

    department(const department &_other) : v_(std::move(_other.clone().v_)) {}

    department(department &&_other) noexcept : v_(std::move(_other.v_)) {}

    department &operator=(const department &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    department &operator=(department &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    department clone() const {
      const auto &[a0, a1] = std::get<Mk_department>(this->v());
      return department(Mk_department{
          a0, a1 ? std::make_unique<List<MutualRecord::employee>>(a1->clone())
                 : nullptr});
    }

    // CREATORS
    static department mk_department(unsigned int a0, List<employee> a1) {
      return department(
          Mk_department{a0, std::make_unique<List<employee>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct employee {
    // TYPES
    struct Mk_employee {
      unsigned int a0;
      unsigned int a1;
    };

    using variant_t = std::variant<Mk_employee>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    employee() {}

    explicit employee(Mk_employee _v) : v_(std::move(_v)) {}

    employee(const employee &_other) : v_(std::move(_other.clone().v_)) {}

    employee(employee &&_other) noexcept : v_(std::move(_other.v_)) {}

    employee &operator=(const employee &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    employee &operator=(employee &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    employee clone() const {
      const auto &[a0, a1] = std::get<Mk_employee>(this->v());
      return employee(Mk_employee{a0, a1});
    }

    // CREATORS
    static employee mk_employee(unsigned int a0, unsigned int a1) {
      return employee(Mk_employee{a0, a1});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, List<employee> &>
  static T1 department_rect(F0 &&f, const department &d) {
    const auto &[a0, a1] = std::get<typename department::Mk_department>(d.v());
    return f(a0, *a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, List<employee> &>
  static T1 department_rec(F0 &&f, const department &d) {
    const auto &[a0, a1] = std::get<typename department::Mk_department>(d.v());
    return f(a0, *a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &>
  static T1 employee_rect(F0 &&f, const employee &e) {
    const auto &[a0, a1] = std::get<typename employee::Mk_employee>(e.v());
    return f(a0, a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &>
  static T1 employee_rec(F0 &&f, const employee &e) {
    const auto &[a0, a1] = std::get<typename employee::Mk_employee>(e.v());
    return f(a0, a1);
  }

  static unsigned int dept_id(const department &d);
  static List<employee> dept_employees(const department &d);
  static unsigned int emp_id(const employee &e);
  static unsigned int emp_salary(const employee &e);
  static unsigned int dept_total_salary(const department &d);
  static unsigned int emp_list_salary(const List<employee> &l);
  static unsigned int dept_count(const department &d);
  static unsigned int emp_list_count(const List<employee> &l);
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
