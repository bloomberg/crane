#include <valid_layout_window.h>

#include <memory>
#include <type_traits>

__attribute__((pure)) bool ValidLayoutWindow::valid_layoutb(
    const std::shared_ptr<ValidLayoutWindow::layout> &l) {
  return (l->base_addr + l->code_size) <= 4096u;
}
