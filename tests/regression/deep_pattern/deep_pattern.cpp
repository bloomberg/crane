#include "deep_pattern.h"

unsigned int
DeepPattern::list_deep_match(const DeepPattern::list<DeepPattern::tree> &l) {
  if (std::holds_alternative<
          typename DeepPattern::list<DeepPattern::tree>::Nil>(l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename DeepPattern::list<DeepPattern::tree>::Cons>(l.v());
    if (std::holds_alternative<typename DeepPattern::tree::Leaf>(a0.v())) {
      const auto &[a00] = std::get<typename DeepPattern::tree::Leaf>(a0.v());
      auto &&_sv1 = *a1;
      if (std::holds_alternative<
              typename DeepPattern::list<DeepPattern::tree>::Nil>(_sv1.v())) {
        return a00;
      } else {
        const auto &[a01, a11] =
            std::get<typename DeepPattern::list<DeepPattern::tree>::Cons>(
                _sv1.v());
        if (std::holds_alternative<typename DeepPattern::tree::Leaf>(a01.v())) {
          const auto &[a02] =
              std::get<typename DeepPattern::tree::Leaf>(a01.v());
          auto &&_sv = *a11;
          if (std::holds_alternative<
                  typename DeepPattern::list<DeepPattern::tree>::Nil>(
                  _sv.v())) {
            return (a00 + a02);
          } else {
            return 0u;
          }
        } else {
          return 0u;
        }
      }
    } else {
      const auto &[a00, a10] =
          std::get<typename DeepPattern::tree::Node>(a0.v());
      auto &&_sv1 = *a00;
      if (std::holds_alternative<typename DeepPattern::tree::Leaf>(_sv1.v())) {
        const auto &[a01] =
            std::get<typename DeepPattern::tree::Leaf>(_sv1.v());
        auto &&_sv2 = *a10;
        if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                _sv2.v())) {
          const auto &[a02] =
              std::get<typename DeepPattern::tree::Leaf>(_sv2.v());
          auto &&_sv3 = *a1;
          if (std::holds_alternative<
                  typename DeepPattern::list<DeepPattern::tree>::Nil>(
                  _sv3.v())) {
            return 0u;
          } else {
            const auto &[a03, a13] =
                std::get<typename DeepPattern::list<DeepPattern::tree>::Cons>(
                    _sv3.v());
            if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                    a03.v())) {
              const auto &[a04] =
                  std::get<typename DeepPattern::tree::Leaf>(a03.v());
              auto &&_sv = *a13;
              if (std::holds_alternative<
                      typename DeepPattern::list<DeepPattern::tree>::Nil>(
                      _sv.v())) {
                return ((a01 + a02) + a04);
              } else {
                return 0u;
              }
            } else {
              const auto &[a04, a14] =
                  std::get<typename DeepPattern::tree::Node>(a03.v());
              auto &&_sv5 = *a04;
              if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                      _sv5.v())) {
                const auto &[a05] =
                    std::get<typename DeepPattern::tree::Leaf>(_sv5.v());
                auto &&_sv6 = *a14;
                if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                        _sv6.v())) {
                  const auto &[a06] =
                      std::get<typename DeepPattern::tree::Leaf>(_sv6.v());
                  auto &&_sv = *a13;
                  if (std::holds_alternative<
                          typename DeepPattern::list<DeepPattern::tree>::Nil>(
                          _sv.v())) {
                    return (((a01 + a02) + a05) + a06);
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
