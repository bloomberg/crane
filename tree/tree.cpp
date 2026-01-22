#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <tree.h>
#include <variant>

namespace bool0 {
std::shared_ptr<bool0> true0::make() {
  return std::make_shared<bool0>(true0{});
}
std::shared_ptr<bool0> false0::make() {
  return std::make_shared<bool0>(false0{});
}
}; // namespace bool0

namespace nat {
std::shared_ptr<nat> O::make() { return std::make_shared<nat>(O{}); }
std::shared_ptr<nat> S::make(std::shared_ptr<nat> _a0) {
  return std::make_shared<nat>(S{_a0});
}
}; // namespace nat

namespace list {};

std::shared_ptr<nat::nat> add(const std::shared_ptr<nat::nat> n,
                              const std::shared_ptr<nat::nat> m) {
  return std::visit(
      Overloaded{
          [&](const nat::O _args) -> std::shared_ptr<nat::nat> { return m; },
          [&](const nat::S _args) -> std::shared_ptr<nat::nat> {
            std::shared_ptr<nat::nat> p = _args._a0;
            return nat::S::make(add(p, m));
          }},
      *n);
}

std::shared_ptr<nat::nat> max(const std::shared_ptr<nat::nat> n,
                              const std::shared_ptr<nat::nat> m) {
  return std::visit(
      Overloaded{
          [&](const nat::O _args) -> std::shared_ptr<nat::nat> { return m; },
          [&](const nat::S _args) -> std::shared_ptr<nat::nat> {
            std::shared_ptr<nat::nat> n_ = _args._a0;
            return std::visit(
                Overloaded{
                    [&](const nat::O _args) -> std::shared_ptr<nat::nat> {
                      return n;
                    },
                    [&](const nat::S _args) -> std::shared_ptr<nat::nat> {
                      std::shared_ptr<nat::nat> m_ = _args._a0;
                      return nat::S::make(max(n_, m_));
                    }},
                *m);
          }},
      *n);
}

namespace Tree {
namespace tree {};

}; // namespace Tree
