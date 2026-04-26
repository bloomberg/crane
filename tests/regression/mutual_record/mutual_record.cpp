#include <mutual_record.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
MutualRecord::dept_id(const MutualRecord::department &d) {
  const auto &[d_a0, d_a1] =
      std::get<typename MutualRecord::department::Mk_department>(d.v());
  return d_a0;
}

__attribute__((pure)) List<MutualRecord::employee>
MutualRecord::dept_employees(const MutualRecord::department &d) {
  const auto &[d_a0, d_a1] =
      std::get<typename MutualRecord::department::Mk_department>(d.v());
  return clone_as_value<List<MutualRecord::employee>>(d_a1);
}

__attribute__((pure)) unsigned int
MutualRecord::emp_id(const MutualRecord::employee &e) {
  const auto &[d_a0, d_a1] =
      std::get<typename MutualRecord::employee::Mk_employee>(e.v());
  return d_a0;
}

__attribute__((pure)) unsigned int
MutualRecord::emp_salary(const MutualRecord::employee &e) {
  const auto &[d_a0, d_a1] =
      std::get<typename MutualRecord::employee::Mk_employee>(e.v());
  return d_a1;
}

__attribute__((pure)) unsigned int
MutualRecord::dept_total_salary(const MutualRecord::department &d) {
  const auto &[d_a0, d_a1] =
      std::get<typename MutualRecord::department::Mk_department>(d.v());
  return emp_list_salary(clone_as_value<List<MutualRecord::employee>>(d_a1));
}

__attribute__((pure)) unsigned int
MutualRecord::emp_list_salary(const List<MutualRecord::employee> &l) {
  if (std::holds_alternative<typename List<MutualRecord::employee>::Nil>(
          l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<MutualRecord::employee>::Cons>(l.v());
    return (emp_salary(d_a0) + emp_list_salary(*(d_a1)));
  }
}

__attribute__((pure)) unsigned int
MutualRecord::dept_count(const MutualRecord::department &d) {
  const auto &[d_a0, d_a1] =
      std::get<typename MutualRecord::department::Mk_department>(d.v());
  return emp_list_count(clone_as_value<List<MutualRecord::employee>>(d_a1));
}

__attribute__((pure)) unsigned int
MutualRecord::emp_list_count(const List<MutualRecord::employee> &l) {
  if (std::holds_alternative<typename List<MutualRecord::employee>::Nil>(
          l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<MutualRecord::employee>::Cons>(l.v());
    return (1u + emp_list_count(*(d_a1)));
  }
}
