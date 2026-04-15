#include <drop_head_default.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
DropHeadDefault::head_after_drop(const std::shared_ptr<List<unsigned int>> &rom,
                                 const unsigned int addr) {
  auto &&_sv = drop<unsigned int>(addr, rom);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&_sv->v());
    return _m.d_a0;
  }
}
