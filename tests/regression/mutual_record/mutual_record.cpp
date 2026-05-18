#include "mutual_record.h"

uint64_t MutualRecord::dept_id(const MutualRecord::department &d) {
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

uint64_t MutualRecord::emp_id(const MutualRecord::employee &e) {
  const auto &[a0, a1] =
      std::get<typename MutualRecord::employee::Mk_employee>(e.v());
  return a0;
}

uint64_t MutualRecord::emp_salary(const MutualRecord::employee &e) {
  const auto &[a0, a1] =
      std::get<typename MutualRecord::employee::Mk_employee>(e.v());
  return a1;
}

uint64_t MutualRecord::dept_total_salary(const MutualRecord::department &d) {
  const auto &[a0, a1] =
      std::get<typename MutualRecord::department::Mk_department>(d.v());
  return emp_list_salary(*a1);
}

uint64_t MutualRecord::emp_list_salary(const List<MutualRecord::employee> &l) {
  if (std::holds_alternative<typename List<MutualRecord::employee>::Nil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename List<MutualRecord::employee>::Cons>(l.v());
    return (emp_salary(a0) + emp_list_salary(*a1));
  }
}

uint64_t MutualRecord::dept_count(const MutualRecord::department &d) {
  const auto &[a0, a1] =
      std::get<typename MutualRecord::department::Mk_department>(d.v());
  return emp_list_count(*a1);
}

uint64_t MutualRecord::emp_list_count(const List<MutualRecord::employee> &l) {
  if (std::holds_alternative<typename List<MutualRecord::employee>::Nil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename List<MutualRecord::employee>::Cons>(l.v());
    return (UINT64_C(1) + emp_list_count(*a1));
  }
}
