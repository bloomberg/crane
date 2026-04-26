#include <deep_pattern.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
DeepPattern::list_deep_match(const DeepPattern::list<DeepPattern::tree> &l) {
  if (std::holds_alternative<
          typename DeepPattern::list<DeepPattern::tree>::Nil>(l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename DeepPattern::list<DeepPattern::tree>::Cons>(l.v());
    if (std::holds_alternative<typename DeepPattern::tree::Leaf>(d_a0.v())) {
      const auto &[d_a00] =
          std::get<typename DeepPattern::tree::Leaf>(d_a0.v());
      auto &&_sv1 = *(d_a1);
      if (std::holds_alternative<
              typename DeepPattern::list<DeepPattern::tree>::Nil>(_sv1.v())) {
        return d_a00;
      } else {
        const auto &[d_a01, d_a11] =
            std::get<typename DeepPattern::list<DeepPattern::tree>::Cons>(
                _sv1.v());
        if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                d_a01.v())) {
          const auto &[d_a02] =
              std::get<typename DeepPattern::tree::Leaf>(d_a01.v());
          auto &&_sv = *(d_a11);
          if (std::holds_alternative<
                  typename DeepPattern::list<DeepPattern::tree>::Nil>(
                  _sv.v())) {
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
          std::get<typename DeepPattern::tree::Node>(d_a0.v());
      auto &&_sv1 = *(d_a00);
      if (std::holds_alternative<typename DeepPattern::tree::Leaf>(_sv1.v())) {
        const auto &[d_a01] =
            std::get<typename DeepPattern::tree::Leaf>(_sv1.v());
        auto &&_sv2 = *(d_a10);
        if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                _sv2.v())) {
          const auto &[d_a02] =
              std::get<typename DeepPattern::tree::Leaf>(_sv2.v());
          auto &&_sv3 = *(d_a1);
          if (std::holds_alternative<
                  typename DeepPattern::list<DeepPattern::tree>::Nil>(
                  _sv3.v())) {
            return 0u;
          } else {
            const auto &[d_a03, d_a13] =
                std::get<typename DeepPattern::list<DeepPattern::tree>::Cons>(
                    _sv3.v());
            if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                    d_a03.v())) {
              const auto &[d_a04] =
                  std::get<typename DeepPattern::tree::Leaf>(d_a03.v());
              auto &&_sv = *(d_a13);
              if (std::holds_alternative<
                      typename DeepPattern::list<DeepPattern::tree>::Nil>(
                      _sv.v())) {
                return ((d_a01 + d_a02) + d_a04);
              } else {
                return 0u;
              }
            } else {
              const auto &[d_a04, d_a14] =
                  std::get<typename DeepPattern::tree::Node>(d_a03.v());
              auto &&_sv5 = *(d_a04);
              if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                      _sv5.v())) {
                const auto &[d_a05] =
                    std::get<typename DeepPattern::tree::Leaf>(_sv5.v());
                auto &&_sv6 = *(d_a14);
                if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                        _sv6.v())) {
                  const auto &[d_a06] =
                      std::get<typename DeepPattern::tree::Leaf>(_sv6.v());
                  auto &&_sv = *(d_a13);
                  if (std::holds_alternative<
                          typename DeepPattern::list<DeepPattern::tree>::Nil>(
                          _sv.v())) {
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
