#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <valid_layout_window.h>
#include <variant>

bool ValidLayoutWindow::valid_layoutb(
    const std::shared_ptr<ValidLayoutWindow::layout> &l) {
  return ((l->base_addr + l->code_size) <= 4096u);
}
