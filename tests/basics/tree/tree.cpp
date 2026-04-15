#include <tree.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Nat::nat> Nat::max(std::shared_ptr<Nat::nat> n,
                                   std::shared_ptr<Nat::nat> m) {
  if (std::holds_alternative<typename Nat::nat::O>(n->v())) {
    return m;
  } else {
    const auto &[d_a0] = std::get<typename Nat::nat::S>(n->v());
    if (std::holds_alternative<typename Nat::nat::O>(m->v())) {
      return n;
    } else {
      if (m.use_count() == 1) {
        auto &_rf = std::get<typename Nat::nat::S>(m->v_mut());
        std::shared_ptr<Nat::nat> m_ = std::move(_rf.d_a0);
        _rf.d_a0 = Nat::max(std::move(d_a0), m_);
        return m;
      } else {
        const auto &[d_a00] = std::get<typename Nat::nat::S>(m->v());
        return Nat::nat::s(Nat::max(d_a0, d_a00));
      }
    }
  }
}
