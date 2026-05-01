#include <valid_layout_window.h>

bool ValidLayoutWindow::valid_layoutb(const ValidLayoutWindow::layout &l) {
  return (l.base_addr + l.code_size) <= 4096u;
}
