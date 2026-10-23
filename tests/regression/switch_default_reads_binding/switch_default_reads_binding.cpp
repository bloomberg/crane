#include "switch_default_reads_binding.h"

/// A binding read only in a switch's default arm: dead-binding removal
/// must see the arm, or the declaration goes and the arm names nothing.
SwitchDefaultReadsBinding::shade
SwitchDefaultReadsBinding::pick(SwitchDefaultReadsBinding::Color c) {
  SwitchDefaultReadsBinding::Color k = Color::GREEN;
  switch (c) {
  case Color::RED: {
    return shade::shade0(Color::RED, Color::RED);
  }
  default: {
    return shade::shade0(k, k);
  }
  }
}
