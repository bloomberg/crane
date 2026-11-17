#pragma once

#include <memory>
#include <optional>

struct OptionLetNoneBug {
  static inline const std::optional<bool> bug = std::optional<bool>();
};
