#include <drop_head_default.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
DropHeadDefault::head_after_drop(const List<unsigned int> &rom,
                                 const unsigned int &addr) {
  auto &&_sv = drop<unsigned int>(addr, rom);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv.v());
    return d_a0;
  }
}
