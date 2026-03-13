#include <mutual_record.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
MutualRecord::dept_id(const std::shared_ptr<MutualRecord::department> &d) {
  return std::visit(
      Overloaded{
          [](const typename MutualRecord::department::Mk_department _args)
              -> unsigned int {
            unsigned int id = _args.d_a0;
            return std::move(id);
          }},
      d->v());
}

std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>>
MutualRecord::dept_employees(
    const std::shared_ptr<MutualRecord::department> &d) {
  return std::visit(
      Overloaded{
          [](const typename MutualRecord::department::Mk_department _args)
              -> std::shared_ptr<
                  List<std::shared_ptr<MutualRecord::employee>>> {
            std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>>
                emps = _args.d_a1;
            return std::move(emps);
          }},
      d->v());
}

__attribute__((pure)) unsigned int
MutualRecord::emp_id(const std::shared_ptr<MutualRecord::employee> &e) {
  return std::visit(
      Overloaded{[](const typename MutualRecord::employee::Mk_employee _args)
                     -> unsigned int {
        unsigned int id = _args.d_a0;
        return std::move(id);
      }},
      e->v());
}

__attribute__((pure)) unsigned int
MutualRecord::emp_salary(const std::shared_ptr<MutualRecord::employee> &e) {
  return std::visit(
      Overloaded{[](const typename MutualRecord::employee::Mk_employee _args)
                     -> unsigned int {
        unsigned int sal = _args.d_a1;
        return std::move(sal);
      }},
      e->v());
}

__attribute__((pure)) unsigned int MutualRecord::dept_total_salary(
    const std::shared_ptr<MutualRecord::department> &d) {
  return std::visit(
      Overloaded{[](const typename MutualRecord::department::Mk_department
                        _args) -> unsigned int {
        std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>> emps =
            _args.d_a1;
        return emp_list_salary(std::move(emps));
      }},
      d->v());
}

__attribute__((pure)) unsigned int MutualRecord::emp_list_salary(
    const std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<MutualRecord::employee>>::Nil
                 _args) -> unsigned int { return 0u; },
          [](const typename List<std::shared_ptr<MutualRecord::employee>>::Cons
                 _args) -> unsigned int {
            std::shared_ptr<MutualRecord::employee> e = _args.d_a0;
            std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>>
                rest = _args.d_a1;
            return (emp_salary(std::move(e)) +
                    emp_list_salary(std::move(rest)));
          }},
      l->v());
}

__attribute__((pure)) unsigned int
MutualRecord::dept_count(const std::shared_ptr<MutualRecord::department> &d) {
  return std::visit(
      Overloaded{[](const typename MutualRecord::department::Mk_department
                        _args) -> unsigned int {
        std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>> emps =
            _args.d_a1;
        return emp_list_count(std::move(emps));
      }},
      d->v());
}

__attribute__((pure)) unsigned int MutualRecord::emp_list_count(
    const std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<MutualRecord::employee>>::Nil
                 _args) -> unsigned int { return 0u; },
          [](const typename List<std::shared_ptr<MutualRecord::employee>>::Cons
                 _args) -> unsigned int {
            std::shared_ptr<List<std::shared_ptr<MutualRecord::employee>>>
                rest = _args.d_a1;
            return (1u + emp_list_count(std::move(rest)));
          }},
      l->v());
}
