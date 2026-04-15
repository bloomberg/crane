#include <deep_pattern.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int DeepPattern::list_deep_match(
    const std::shared_ptr<DeepPattern::list<std::shared_ptr<DeepPattern::tree>>>
        &l) {
  if (std::holds_alternative<
          typename DeepPattern::list<std::shared_ptr<DeepPattern::tree>>::Nil>(
          l->v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] = std::get<
        typename DeepPattern::list<std::shared_ptr<DeepPattern::tree>>::Cons>(
        l->v());
    if (std::holds_alternative<typename DeepPattern::tree::Leaf>(d_a0->v())) {
      const auto &[d_a00] =
          std::get<typename DeepPattern::tree::Leaf>(d_a0->v());
      if (std::holds_alternative<typename DeepPattern::list<
              std::shared_ptr<DeepPattern::tree>>::Nil>(d_a1->v())) {
        return d_a00;
      } else {
        const auto &[d_a01, d_a11] = std::get<typename DeepPattern::list<
            std::shared_ptr<DeepPattern::tree>>::Cons>(d_a1->v());
        if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                d_a01->v())) {
          const auto &[d_a02] =
              std::get<typename DeepPattern::tree::Leaf>(d_a01->v());
          if (std::holds_alternative<typename DeepPattern::list<
                  std::shared_ptr<DeepPattern::tree>>::Nil>(d_a11->v())) {
            return (d_a00 + d_a02);
          } else {
            return 0u;
          }
        } else {
          return 0u;
        }
      }
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename DeepPattern::tree::Node>(d_a0->v());
      if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
              d_a00->v())) {
        const auto &[d_a01] =
            std::get<typename DeepPattern::tree::Leaf>(d_a00->v());
        if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                d_a10->v())) {
          const auto &[d_a02] =
              std::get<typename DeepPattern::tree::Leaf>(d_a10->v());
          if (std::holds_alternative<typename DeepPattern::list<
                  std::shared_ptr<DeepPattern::tree>>::Nil>(d_a1->v())) {
            return 0u;
          } else {
            const auto &[d_a03, d_a13] = std::get<typename DeepPattern::list<
                std::shared_ptr<DeepPattern::tree>>::Cons>(d_a1->v());
            if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                    d_a03->v())) {
              const auto &[d_a04] =
                  std::get<typename DeepPattern::tree::Leaf>(d_a03->v());
              if (std::holds_alternative<typename DeepPattern::list<
                      std::shared_ptr<DeepPattern::tree>>::Nil>(d_a13->v())) {
                return ((d_a01 + d_a02) + d_a04);
              } else {
                return 0u;
              }
            } else {
              const auto &[d_a04, d_a14] =
                  std::get<typename DeepPattern::tree::Node>(d_a03->v());
              if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                      d_a04->v())) {
                const auto &[d_a05] =
                    std::get<typename DeepPattern::tree::Leaf>(d_a04->v());
                if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                        d_a14->v())) {
                  const auto &[d_a06] =
                      std::get<typename DeepPattern::tree::Leaf>(d_a14->v());
                  if (std::holds_alternative<typename DeepPattern::list<
                          std::shared_ptr<DeepPattern::tree>>::Nil>(
                          d_a13->v())) {
                    return (((d_a01 + d_a02) + d_a05) + d_a06);
                  } else {
                    return 0u;
                  }
                } else {
                  return 0u;
                }
              } else {
                return 0u;
              }
            }
          }
        } else {
          return 0u;
        }
      } else {
        return 0u;
      }
    }
  }
}

std::shared_ptr<DeepPattern::tree>
DeepPattern::as_pattern_test(std::shared_ptr<DeepPattern::tree> t) {
  return t;
}
