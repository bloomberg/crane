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
    const auto &_m = *std::get_if<
        typename DeepPattern::list<std::shared_ptr<DeepPattern::tree>>::Cons>(
        &l->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename DeepPattern::tree::Leaf>(_sv0->v())) {
      const auto &_m0 =
          *std::get_if<typename DeepPattern::tree::Leaf>(&_sv0->v());
      auto &&_sv1 = _m.d_a1;
      if (std::holds_alternative<typename DeepPattern::list<
              std::shared_ptr<DeepPattern::tree>>::Nil>(_sv1->v())) {
        return _m0.d_a0;
      } else {
        const auto &_m1 = *std::get_if<typename DeepPattern::list<
            std::shared_ptr<DeepPattern::tree>>::Cons>(&_sv1->v());
        auto &&_sv2 = _m1.d_a0;
        if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                _sv2->v())) {
          const auto &_m2 =
              *std::get_if<typename DeepPattern::tree::Leaf>(&_sv2->v());
          auto &&_sv = _m1.d_a1;
          if (std::holds_alternative<typename DeepPattern::list<
                  std::shared_ptr<DeepPattern::tree>>::Nil>(_sv->v())) {
            return (_m0.d_a0 + _m2.d_a0);
          } else {
            return 0u;
          }
        } else {
          return 0u;
        }
      }
    } else {
      const auto &_m0 =
          *std::get_if<typename DeepPattern::tree::Node>(&_sv0->v());
      auto &&_sv1 = _m0.d_a0;
      if (std::holds_alternative<typename DeepPattern::tree::Leaf>(_sv1->v())) {
        const auto &_m1 =
            *std::get_if<typename DeepPattern::tree::Leaf>(&_sv1->v());
        auto &&_sv2 = _m0.d_a1;
        if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                _sv2->v())) {
          const auto &_m2 =
              *std::get_if<typename DeepPattern::tree::Leaf>(&_sv2->v());
          auto &&_sv3 = _m.d_a1;
          if (std::holds_alternative<typename DeepPattern::list<
                  std::shared_ptr<DeepPattern::tree>>::Nil>(_sv3->v())) {
            return 0u;
          } else {
            const auto &_m3 = *std::get_if<typename DeepPattern::list<
                std::shared_ptr<DeepPattern::tree>>::Cons>(&_sv3->v());
            auto &&_sv4 = _m3.d_a0;
            if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                    _sv4->v())) {
              const auto &_m4 =
                  *std::get_if<typename DeepPattern::tree::Leaf>(&_sv4->v());
              auto &&_sv = _m3.d_a1;
              if (std::holds_alternative<typename DeepPattern::list<
                      std::shared_ptr<DeepPattern::tree>>::Nil>(_sv->v())) {
                return ((_m1.d_a0 + _m2.d_a0) + _m4.d_a0);
              } else {
                return 0u;
              }
            } else {
              const auto &_m4 =
                  *std::get_if<typename DeepPattern::tree::Node>(&_sv4->v());
              auto &&_sv5 = _m4.d_a0;
              if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                      _sv5->v())) {
                const auto &_m5 =
                    *std::get_if<typename DeepPattern::tree::Leaf>(&_sv5->v());
                auto &&_sv6 = _m4.d_a1;
                if (std::holds_alternative<typename DeepPattern::tree::Leaf>(
                        _sv6->v())) {
                  const auto &_m6 =
                      *std::get_if<typename DeepPattern::tree::Leaf>(
                          &_sv6->v());
                  auto &&_sv = _m3.d_a1;
                  if (std::holds_alternative<typename DeepPattern::list<
                          std::shared_ptr<DeepPattern::tree>>::Nil>(_sv->v())) {
                    return (((_m1.d_a0 + _m2.d_a0) + _m5.d_a0) + _m6.d_a0);
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
