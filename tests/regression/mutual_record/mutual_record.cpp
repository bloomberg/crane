#include <mutual_record.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
MutualRecord::dept_id(const std::shared_ptr<MutualRecord::department> &d) {
  return std::visit(
      Overloaded{
          [](const typename MutualRecord::department::Mk_department &_args)
              -> unsigned int { return _args.d_a0; }},
      d->v());
}

std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>>
MutualRecord::dept_employees(
    const std::shared_ptr<MutualRecord::department> &d) {
  return std::visit(
      Overloaded{
          [](const typename MutualRecord::department::Mk_department &_args)
              -> std::shared_ptr<
                  List<std::shared_ptr<MutualRecord::employee>>> {
            return _args.d_a1;
          }},
      d->v());
}

__attribute__((pure)) unsigned int
MutualRecord::emp_id(const std::shared_ptr<MutualRecord::employee> &e) {
  return std::visit(
      Overloaded{[](const typename MutualRecord::employee::Mk_employee &_args)
                     -> unsigned int { return _args.d_a0; }},
      e->v());
}

__attribute__((pure)) unsigned int
MutualRecord::emp_salary(const std::shared_ptr<MutualRecord::employee> &e) {
  return std::visit(
      Overloaded{[](const typename MutualRecord::employee::Mk_employee &_args)
                     -> unsigned int { return _args.d_a1; }},
      e->v());
}

__attribute__((pure)) unsigned int MutualRecord::dept_total_salary(
    const std::shared_ptr<MutualRecord::department> &d) {
  return std::visit(
      Overloaded{
          [](const typename MutualRecord::department::Mk_department &_args)
              -> unsigned int { return emp_list_salary(_args.d_a1); }},
      d->v());
}

__attribute__((pure)) unsigned int MutualRecord::emp_list_salary(
    const std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<MutualRecord::employee>>::Nil
                 &) -> unsigned int { return 0u; },
          [](const typename List<std::shared_ptr<MutualRecord::employee>>::Cons
                 &_args) -> unsigned int {
            return (emp_salary(_args.d_a0) + emp_list_salary(_args.d_a1));
          }},
      l->v());
}

__attribute__((pure)) unsigned int
MutualRecord::dept_count(const std::shared_ptr<MutualRecord::department> &d) {
  return std::visit(
      Overloaded{
          [](const typename MutualRecord::department::Mk_department &_args)
              -> unsigned int { return emp_list_count(_args.d_a1); }},
      d->v());
}

__attribute__((pure)) unsigned int MutualRecord::emp_list_count(
    const std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<MutualRecord::employee>>::Nil
                 &) -> unsigned int { return 0u; },
          [](const typename List<std::shared_ptr<MutualRecord::employee>>::Cons
                 &_args) -> unsigned int {
            return (1u + emp_list_count(_args.d_a1));
          }},
      l->v());
}
