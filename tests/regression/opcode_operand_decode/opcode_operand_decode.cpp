#include "opcode_operand_decode.h"

OpcodeOperandDecode::Instruction OpcodeOperandDecode::decode(uint64_t b1,
                                                             uint64_t) {
  uint64_t opcode = (UINT64_C(16) ? b1 / UINT64_C(16) : 0);
  uint64_t operand = (UINT64_C(16) ? b1 % UINT64_C(16) : b1);
  if (opcode <= 0) {
    return Instruction::NOP_;
  } else {
    uint64_t n = opcode - 1;
    if (n <= 0) {
      return Instruction::NOP_;
    } else {
      uint64_t n0 = n - 1;
      if (n0 <= 0) {
        return Instruction::NOP_;
      } else {
        uint64_t n1 = n0 - 1;
        if (n1 <= 0) {
          return Instruction::NOP_;
        } else {
          uint64_t n2 = n1 - 1;
          if (n2 <= 0) {
            return Instruction::NOP_;
          } else {
            uint64_t n3 = n2 - 1;
            if (n3 <= 0) {
              return Instruction::NOP_;
            } else {
              uint64_t n4 = n3 - 1;
              if (n4 <= 0) {
                return Instruction::NOP_;
              } else {
                uint64_t n5 = n4 - 1;
                if (n5 <= 0) {
                  return Instruction::NOP_;
                } else {
                  uint64_t n6 = n5 - 1;
                  if (n6 <= 0) {
                    return Instruction::NOP_;
                  } else {
                    uint64_t n7 = n6 - 1;
                    if (n7 <= 0) {
                      return Instruction::NOP_;
                    } else {
                      uint64_t n8 = n7 - 1;
                      if (n8 <= 0) {
                        return Instruction::NOP_;
                      } else {
                        uint64_t n9 = n8 - 1;
                        if (n9 <= 0) {
                          return Instruction::NOP_;
                        } else {
                          uint64_t n10 = n9 - 1;
                          if (n10 <= 0) {
                            return Instruction::NOP_;
                          } else {
                            uint64_t n11 = n10 - 1;
                            if (n11 <= 0) {
                              return Instruction::NOP_;
                            } else {
                              uint64_t n12 = n11 - 1;
                              if (n12 <= 0) {
                                if (operand <= 0) {
                                  return Instruction::WRM_;
                                } else {
                                  uint64_t n13 = operand - 1;
                                  if (n13 <= 0) {
                                    return Instruction::NOP_;
                                  } else {
                                    uint64_t n14 = n13 - 1;
                                    if (n14 <= 0) {
                                      return Instruction::WRR_;
                                    } else {
                                      uint64_t n15 = n14 - 1;
                                      if (n15 <= 0) {
                                        return Instruction::NOP_;
                                      } else {
                                        uint64_t n16 = n15 - 1;
                                        if (n16 <= 0) {
                                          return Instruction::NOP_;
                                        } else {
                                          uint64_t n17 = n16 - 1;
                                          if (n17 <= 0) {
                                            return Instruction::NOP_;
                                          } else {
                                            uint64_t n18 = n17 - 1;
                                            if (n18 <= 0) {
                                              return Instruction::NOP_;
                                            } else {
                                              uint64_t n19 = n18 - 1;
                                              if (n19 <= 0) {
                                                return Instruction::NOP_;
                                              } else {
                                                uint64_t n20 = n19 - 1;
                                                if (n20 <= 0) {
                                                  return Instruction::NOP_;
                                                } else {
                                                  uint64_t n21 = n20 - 1;
                                                  if (n21 <= 0) {
                                                    return Instruction::RDM_;
                                                  } else {
                                                    uint64_t _x0 = n21 - 1;
                                                    return Instruction::NOP_;
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              } else {
                                uint64_t n13 = n12 - 1;
                                if (n13 <= 0) {
                                  if (operand <= 0) {
                                    return Instruction::NOP_;
                                  } else {
                                    uint64_t n14 = operand - 1;
                                    if (n14 <= 0) {
                                      return Instruction::NOP_;
                                    } else {
                                      uint64_t n15 = n14 - 1;
                                      if (n15 <= 0) {
                                        return Instruction::NOP_;
                                      } else {
                                        uint64_t n16 = n15 - 1;
                                        if (n16 <= 0) {
                                          return Instruction::NOP_;
                                        } else {
                                          uint64_t n17 = n16 - 1;
                                          if (n17 <= 0) {
                                            return Instruction::NOP_;
                                          } else {
                                            uint64_t n18 = n17 - 1;
                                            if (n18 <= 0) {
                                              return Instruction::NOP_;
                                            } else {
                                              uint64_t n19 = n18 - 1;
                                              if (n19 <= 0) {
                                                return Instruction::NOP_;
                                              } else {
                                                uint64_t n20 = n19 - 1;
                                                if (n20 <= 0) {
                                                  return Instruction::NOP_;
                                                } else {
                                                  uint64_t n21 = n20 - 1;
                                                  if (n21 <= 0) {
                                                    return Instruction::NOP_;
                                                  } else {
                                                    uint64_t n22 = n21 - 1;
                                                    if (n22 <= 0) {
                                                      return Instruction::NOP_;
                                                    } else {
                                                      uint64_t n23 = n22 - 1;
                                                      if (n23 <= 0) {
                                                        return Instruction::
                                                            NOP_;
                                                      } else {
                                                        uint64_t n24 = n23 - 1;
                                                        if (n24 <= 0) {
                                                          return Instruction::
                                                              NOP_;
                                                        } else {
                                                          uint64_t n25 =
                                                              n24 - 1;
                                                          if (n25 <= 0) {
                                                            return Instruction::
                                                                NOP_;
                                                          } else {
                                                            uint64_t n26 =
                                                                n25 - 1;
                                                            if (n26 <= 0) {
                                                              return Instruction::
                                                                  DCL_;
                                                            } else {
                                                              uint64_t _x0 =
                                                                  n26 - 1;
                                                              return Instruction::
                                                                  NOP_;
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                } else {
                                  uint64_t _x0 = n13 - 1;
                                  return Instruction::NOP_;
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}
