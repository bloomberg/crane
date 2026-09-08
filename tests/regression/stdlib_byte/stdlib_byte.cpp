#include "stdlib_byte.h"

std::pair<
    bool,
    std::pair<
        bool,
        std::pair<
            bool,
            std::pair<
                bool,
                std::pair<bool, std::pair<bool, std::pair<bool, bool>>>>>>>
Byte_Mod::to_bits(Byte b0) {
  switch (b0) {
  case Byte::X00: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false, std::make_pair(
                           false, std::make_pair(
                                      false, std::make_pair(
                                                 false, std::make_pair(
                                                            false, false)))))));
  }
  case Byte::X01: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false, std::make_pair(
                           false, std::make_pair(
                                      false, std::make_pair(
                                                 false, std::make_pair(
                                                            false, false)))))));
  }
  case Byte::X02: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false, std::make_pair(
                           false, std::make_pair(
                                      false, std::make_pair(
                                                 false, std::make_pair(
                                                            false, false)))))));
  }
  case Byte::X03: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false, std::make_pair(
                           false, std::make_pair(
                                      false, std::make_pair(
                                                 false, std::make_pair(
                                                            false, false)))))));
  }
  case Byte::X04: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          false, std::make_pair(
                                     false, std::make_pair(
                                                false, std::make_pair(
                                                           false, false)))))));
  }
  case Byte::X05: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          false, std::make_pair(
                                     false, std::make_pair(
                                                false, std::make_pair(
                                                           false, false)))))));
  }
  case Byte::X06: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          false, std::make_pair(
                                     false, std::make_pair(
                                                false, std::make_pair(
                                                           false, false)))))));
  }
  case Byte::X07: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          false, std::make_pair(
                                     false, std::make_pair(
                                                false, std::make_pair(
                                                           false, false)))))));
  }
  case Byte::X08: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false, std::make_pair(
                           true, std::make_pair(
                                     false, std::make_pair(
                                                false, std::make_pair(
                                                           false, false)))))));
  }
  case Byte::X09: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false, std::make_pair(
                           true, std::make_pair(
                                     false, std::make_pair(
                                                false, std::make_pair(
                                                           false, false)))))));
  }
  case Byte::X0A: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false, std::make_pair(
                           true, std::make_pair(
                                     false, std::make_pair(
                                                false, std::make_pair(
                                                           false, false)))))));
  }
  case Byte::X0B: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false, std::make_pair(
                           true, std::make_pair(
                                     false, std::make_pair(
                                                false, std::make_pair(
                                                           false, false)))))));
  }
  case Byte::X0C: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false, std::make_pair(
                                               false, std::make_pair(
                                                          false, false)))))));
  }
  case Byte::X0D: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false, std::make_pair(
                                               false, std::make_pair(
                                                          false, false)))))));
  }
  case Byte::X0E: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false, std::make_pair(
                                               false, std::make_pair(
                                                          false, false)))))));
  }
  case Byte::X0F: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false, std::make_pair(
                                               false, std::make_pair(
                                                          false, false)))))));
  }
  case Byte::X10: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false, std::make_pair(
                           false, std::make_pair(
                                      true, std::make_pair(
                                                false, std::make_pair(
                                                           false, false)))))));
  }
  case Byte::X11: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false, std::make_pair(
                           false, std::make_pair(
                                      true, std::make_pair(
                                                false, std::make_pair(
                                                           false, false)))))));
  }
  case Byte::X12: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false, std::make_pair(
                           false, std::make_pair(
                                      true, std::make_pair(
                                                false, std::make_pair(
                                                           false, false)))))));
  }
  case Byte::X13: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false, std::make_pair(
                           false, std::make_pair(
                                      true, std::make_pair(
                                                false, std::make_pair(
                                                           false, false)))))));
  }
  case Byte::X14: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          false, std::make_pair(
                                     true, std::make_pair(
                                               false, std::make_pair(
                                                          false, false)))))));
  }
  case Byte::X15: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          false, std::make_pair(
                                     true, std::make_pair(
                                               false, std::make_pair(
                                                          false, false)))))));
  }
  case Byte::X16: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          false, std::make_pair(
                                     true, std::make_pair(
                                               false, std::make_pair(
                                                          false, false)))))));
  }
  case Byte::X17: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          false, std::make_pair(
                                     true, std::make_pair(
                                               false, std::make_pair(
                                                          false, false)))))));
  }
  case Byte::X18: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false, std::make_pair(
                           true, std::make_pair(
                                     true, std::make_pair(
                                               false, std::make_pair(
                                                          false, false)))))));
  }
  case Byte::X19: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false, std::make_pair(
                           true, std::make_pair(
                                     true, std::make_pair(
                                               false, std::make_pair(
                                                          false, false)))))));
  }
  case Byte::X1A: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false, std::make_pair(
                           true, std::make_pair(
                                     true, std::make_pair(
                                               false, std::make_pair(
                                                          false, false)))))));
  }
  case Byte::X1B: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false, std::make_pair(
                           true, std::make_pair(
                                     true, std::make_pair(
                                               false, std::make_pair(
                                                          false, false)))))));
  }
  case Byte::X1C: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    true, std::make_pair(
                                              false, std::make_pair(
                                                         false, false)))))));
  }
  case Byte::X1D: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    true, std::make_pair(
                                              false, std::make_pair(
                                                         false, false)))))));
  }
  case Byte::X1E: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    true, std::make_pair(
                                              false, std::make_pair(
                                                         false, false)))))));
  }
  case Byte::X1F: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    true, std::make_pair(
                                              false, std::make_pair(
                                                         false, false)))))));
  }
  case Byte::X20: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X21: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X22: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X23: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X24: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X25: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X26: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X27: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X28: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X29: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X2A: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X2B: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X2C: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X2D: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X2E: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X2F: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X30: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X31: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X32: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X33: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X34: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X35: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X36: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X37: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X38: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X39: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X3A: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X3B: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X3C: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X3D: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X3E: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X3F: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, false)))))));
  }
  case Byte::X40: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X41: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X42: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X43: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X44: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X45: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X46: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X47: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X48: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X49: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X4A: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X4B: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X4C: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X4D: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X4E: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X4F: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X50: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X51: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X52: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X53: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X54: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X55: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X56: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X57: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X58: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X59: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X5A: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X5B: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(true, false)))))));
  }
  case Byte::X5C: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    true, std::make_pair(
                                              false,
                                              std::make_pair(true, false)))))));
  }
  case Byte::X5D: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    true, std::make_pair(
                                              false,
                                              std::make_pair(true, false)))))));
  }
  case Byte::X5E: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    true, std::make_pair(
                                              false,
                                              std::make_pair(true, false)))))));
  }
  case Byte::X5F: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    true, std::make_pair(
                                              false,
                                              std::make_pair(true, false)))))));
  }
  case Byte::X60: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(true, false)))))));
  }
  case Byte::X61: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(true, false)))))));
  }
  case Byte::X62: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(true, false)))))));
  }
  case Byte::X63: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(true, false)))))));
  }
  case Byte::X64: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(true, false)))))));
  }
  case Byte::X65: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(true, false)))))));
  }
  case Byte::X66: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(true, false)))))));
  }
  case Byte::X67: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(true, false)))))));
  }
  case Byte::X68: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(true, false)))))));
  }
  case Byte::X69: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(true, false)))))));
  }
  case Byte::X6A: {
    return std::make_pair(
        false,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X6B: {
    return std::make_pair(
        true,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X6C: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X6D: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X6E: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X6F: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X70: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(true, false)))))));
  }
  case Byte::X71: {
    return std::make_pair(
        true, std::make_pair(
                  false,
                  std::make_pair(
                      false,
                      std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X72: {
    return std::make_pair(
        false,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X73: {
    return std::make_pair(
        true,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X74: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X75: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X76: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X77: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X78: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X79: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X7A: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X7B: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X7C: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X7D: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X7E: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X7F: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, false)))))));
  }
  case Byte::X80: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X81: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X82: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X83: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X84: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X85: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X86: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X87: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X88: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X89: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X8A: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X8B: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X8C: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X8D: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X8E: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X8F: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X90: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X91: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X92: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X93: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X94: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X95: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X96: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X97: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X98: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X99: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X9A: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X9B: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(false, true)))))));
  }
  case Byte::X9C: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    true, std::make_pair(
                                              false,
                                              std::make_pair(false, true)))))));
  }
  case Byte::X9D: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    true, std::make_pair(
                                              false,
                                              std::make_pair(false, true)))))));
  }
  case Byte::X9E: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    true, std::make_pair(
                                              false,
                                              std::make_pair(false, true)))))));
  }
  case Byte::X9F: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    true, std::make_pair(
                                              false,
                                              std::make_pair(false, true)))))));
  }
  case Byte::XA0: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, true)))))));
  }
  case Byte::XA1: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, true)))))));
  }
  case Byte::XA2: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, true)))))));
  }
  case Byte::XA3: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, true)))))));
  }
  case Byte::XA4: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, true)))))));
  }
  case Byte::XA5: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, true)))))));
  }
  case Byte::XA6: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, true)))))));
  }
  case Byte::XA7: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, true)))))));
  }
  case Byte::XA8: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, true)))))));
  }
  case Byte::XA9: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(false, true)))))));
  }
  case Byte::XAA: {
    return std::make_pair(
        false,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XAB: {
    return std::make_pair(
        true,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XAC: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XAD: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XAE: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XAF: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XB0: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(true, std::make_pair(false, true)))))));
  }
  case Byte::XB1: {
    return std::make_pair(
        true, std::make_pair(
                  false,
                  std::make_pair(
                      false,
                      std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XB2: {
    return std::make_pair(
        false,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XB3: {
    return std::make_pair(
        true,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XB4: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XB5: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XB6: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XB7: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XB8: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XB9: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XBA: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XBB: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XBC: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XBD: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XBE: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XBF: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(false, true)))))));
  }
  case Byte::XC0: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, true)))))));
  }
  case Byte::XC1: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, true)))))));
  }
  case Byte::XC2: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, true)))))));
  }
  case Byte::XC3: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, true)))))));
  }
  case Byte::XC4: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, true)))))));
  }
  case Byte::XC5: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, true)))))));
  }
  case Byte::XC6: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, true)))))));
  }
  case Byte::XC7: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, true)))))));
  }
  case Byte::XC8: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, true)))))));
  }
  case Byte::XC9: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true,
                    std::make_pair(
                        false,
                        std::make_pair(false, std::make_pair(true, true)))))));
  }
  case Byte::XCA: {
    return std::make_pair(
        false,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XCB: {
    return std::make_pair(
        true,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XCC: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XCD: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XCE: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XCF: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          true, std::make_pair(
                                    false,
                                    std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XD0: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        true,
                        std::make_pair(false, std::make_pair(true, true)))))));
  }
  case Byte::XD1: {
    return std::make_pair(
        true, std::make_pair(
                  false,
                  std::make_pair(
                      false,
                      std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XD2: {
    return std::make_pair(
        false,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XD3: {
    return std::make_pair(
        true,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XD4: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XD5: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XD6: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XD7: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XD8: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XD9: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XDA: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XDB: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XDC: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XDD: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XDE: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XDF: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        false, std::make_pair(true, true)))))));
  }
  case Byte::XE0: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false,
                    std::make_pair(
                        false,
                        std::make_pair(true, std::make_pair(true, true)))))));
  }
  case Byte::XE1: {
    return std::make_pair(
        true, std::make_pair(
                  false,
                  std::make_pair(
                      false,
                      std::make_pair(
                          false,
                          std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XE2: {
    return std::make_pair(
        false,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          false,
                          std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XE3: {
    return std::make_pair(
        true,
        std::make_pair(
            true, std::make_pair(
                      false,
                      std::make_pair(
                          false,
                          std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XE4: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XE5: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XE6: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XE7: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true, std::make_pair(
                          false,
                          std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XE8: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XE9: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XEA: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XEB: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XEC: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XED: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XEE: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XEF: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              false, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XF0: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false, std::make_pair(
                               true, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XF1: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    false, std::make_pair(
                               true, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XF2: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false, std::make_pair(
                               true, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XF3: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    false, std::make_pair(
                               true, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XF4: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false, std::make_pair(
                               true, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XF5: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    false, std::make_pair(
                               true, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XF6: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false, std::make_pair(
                               true, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XF7: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    false, std::make_pair(
                               true, std::make_pair(
                                         true, std::make_pair(true, true)))))));
  }
  case Byte::XF8: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, true)))))));
  }
  case Byte::XF9: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, true)))))));
  }
  case Byte::XFA: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, true)))))));
  }
  case Byte::XFB: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                false,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, true)))))));
  }
  case Byte::XFC: {
    return std::make_pair(
        false,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, true)))))));
  }
  case Byte::XFD: {
    return std::make_pair(
        true,
        std::make_pair(
            false,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, true)))))));
  }
  case Byte::XFE: {
    return std::make_pair(
        false,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, true)))))));
  }
  case Byte::XFF: {
    return std::make_pair(
        true,
        std::make_pair(
            true,
            std::make_pair(
                true,
                std::make_pair(
                    true, std::make_pair(
                              true, std::make_pair(
                                        true, std::make_pair(true, true)))))));
  }
  default:
    std::unreachable();
  }
}

bool Bool::eqb(bool b1, bool b2) {
  if (b1) {
    if (b2) {
      return true;
    } else {
      return false;
    }
  } else {
    if (b2) {
      return false;
    } else {
      return true;
    }
  }
}

bool Byte0::eqb0(Byte a, Byte b0) {
  auto [a0, p] = Byte_Mod::to_bits(a);
  auto [a1, p0] = std::move(p);
  auto [a2, p1] = std::move(p0);
  auto [a3, p2] = std::move(p1);
  auto [a4, p3] = std::move(p2);
  auto [a5, p4] = std::move(p3);
  auto [a6, a7] = std::move(p4);
  auto [b1, p5] = Byte_Mod::to_bits(b0);
  auto [b2, p6] = std::move(p5);
  auto [b3, p7] = std::move(p6);
  auto [b4, p8] = std::move(p7);
  auto [b5, p9] = std::move(p8);
  auto [b6, p10] = std::move(p9);
  auto [b7, b8] = std::move(p10);
  return (((((((Bool::eqb(a0, b1) && Bool::eqb(a1, b2)) && Bool::eqb(a2, b3)) &&
              Bool::eqb(a3, b4)) &&
             Bool::eqb(a4, b5)) &&
            Bool::eqb(a5, b6)) &&
           Bool::eqb(a6, b7)) &&
          Bool::eqb(a7, b8));
}
