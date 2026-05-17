#include "mutual_record.h"

unsigned int MutualRecord::dept_id(const MutualRecord::department &d) {
  const auto &[a0, a1] =
      std::get<typename MutualRecord::department::Mk_department>(d.v());
  return a0;
}

List<MutualRecord::employee>
MutualRecord::dept_employees(const MutualRecord::department &d) {
  const auto &[a0, a1] =
      std::get<typename MutualRecord::department::Mk_department>(d.v());
  return *a1;
}

unsigned int MutualRecord::emp_id(const MutualRecord::employee &e) {
  const auto &[a0, a1] =
      std::get<typename MutualRecord::employee::Mk_employee>(e.v());
  return a0;
}

unsigned int MutualRecord::emp_salary(const MutualRecord::employee &e) {
  const auto &[a0, a1] =
      std::get<typename MutualRecord::employee::Mk_employee>(e.v());
  return a1;
}

unsigned int
MutualRecord::dept_total_salary(const MutualRecord::department &d) {
  const auto &[a0, a1] =
      std::get<typename MutualRecord::department::Mk_department>(d.v());
  return emp_list_salary(*a1);
}

unsigned int
MutualRecord::emp_list_salary(const List<MutualRecord::employee> &l) {
  if (std::holds_alternative<typename List<MutualRecord::employee>::Nil>(
          l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename List<MutualRecord::employee>::Cons>(l.v());
    return (emp_salary(a0) + emp_list_salary(*a1));
  }
}

unsigned int MutualRecord::dept_count(const MutualRecord::department &d) {
  const auto &[a0, a1] =
      std::get<typename MutualRecord::department::Mk_department>(d.v());
  return emp_list_count(*a1);
}

unsigned int
MutualRecord::emp_list_count(const List<MutualRecord::employee> &l) {
  if (std::holds_alternative<typename List<MutualRecord::employee>::Nil>(
          l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename List<MutualRecord::employee>::Cons>(l.v());
    return (1u + emp_list_count(*a1));
  }
}
