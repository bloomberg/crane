#include <mutual_record.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
MutualRecord::dept_id(const std::shared_ptr<MutualRecord::department> &d) {
  const auto &_m =
      *std::get_if<typename MutualRecord::department::Mk_department>(&d->v());
  return _m.d_a0;
}

std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>>
MutualRecord::dept_employees(
    const std::shared_ptr<MutualRecord::department> &d) {
  const auto &_m =
      *std::get_if<typename MutualRecord::department::Mk_department>(&d->v());
  return _m.d_a1;
}

__attribute__((pure)) unsigned int
MutualRecord::emp_id(const std::shared_ptr<MutualRecord::employee> &e) {
  const auto &_m =
      *std::get_if<typename MutualRecord::employee::Mk_employee>(&e->v());
  return _m.d_a0;
}

__attribute__((pure)) unsigned int
MutualRecord::emp_salary(const std::shared_ptr<MutualRecord::employee> &e) {
  const auto &_m =
      *std::get_if<typename MutualRecord::employee::Mk_employee>(&e->v());
  return _m.d_a1;
}

__attribute__((pure)) unsigned int MutualRecord::dept_total_salary(
    const std::shared_ptr<MutualRecord::department> &d) {
  const auto &_m =
      *std::get_if<typename MutualRecord::department::Mk_department>(&d->v());
  return emp_list_salary(_m.d_a1);
}

__attribute__((pure)) unsigned int MutualRecord::emp_list_salary(
    const std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>> &l) {
  if (std::holds_alternative<
          typename List<std::shared_ptr<MutualRecord::employee>>::Nil>(
          l->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<
        typename List<std::shared_ptr<MutualRecord::employee>>::Cons>(&l->v());
    return (emp_salary(_m.d_a0) + emp_list_salary(_m.d_a1));
  }
}

__attribute__((pure)) unsigned int
MutualRecord::dept_count(const std::shared_ptr<MutualRecord::department> &d) {
  const auto &_m =
      *std::get_if<typename MutualRecord::department::Mk_department>(&d->v());
  return emp_list_count(_m.d_a1);
}

__attribute__((pure)) unsigned int MutualRecord::emp_list_count(
    const std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>> &l) {
  if (std::holds_alternative<
          typename List<std::shared_ptr<MutualRecord::employee>>::Nil>(
          l->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<
        typename List<std::shared_ptr<MutualRecord::employee>>::Cons>(&l->v());
    return (1u + emp_list_count(_m.d_a1));
  }
}
