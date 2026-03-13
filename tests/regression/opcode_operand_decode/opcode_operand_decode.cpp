#include <opcode_operand_decode.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) OpcodeOperandDecode::Instruction
OpcodeOperandDecode::decode(const unsigned int b1, const unsigned int _x) {
  unsigned int opcode = Nat::div(b1, 16u);
  unsigned int operand = (b1 % 16u);
  if (opcode <= 0) {
    return Instruction::e_NOP_;
  } else {
    unsigned int n = opcode - 1;
    if (n <= 0) {
      return Instruction::e_NOP_;
    } else {
      unsigned int n0 = n - 1;
      if (n0 <= 0) {
        return Instruction::e_NOP_;
      } else {
        unsigned int n1 = n0 - 1;
        if (n1 <= 0) {
          return Instruction::e_NOP_;
        } else {
          unsigned int n2 = n1 - 1;
          if (n2 <= 0) {
            return Instruction::e_NOP_;
          } else {
            unsigned int n3 = n2 - 1;
            if (n3 <= 0) {
              return Instruction::e_NOP_;
            } else {
              unsigned int n4 = n3 - 1;
              if (n4 <= 0) {
                return Instruction::e_NOP_;
              } else {
                unsigned int n5 = n4 - 1;
                if (n5 <= 0) {
                  return Instruction::e_NOP_;
                } else {
                  unsigned int n6 = n5 - 1;
                  if (n6 <= 0) {
                    return Instruction::e_NOP_;
                  } else {
                    unsigned int n7 = n6 - 1;
                    if (n7 <= 0) {
                      return Instruction::e_NOP_;
                    } else {
                      unsigned int n8 = n7 - 1;
                      if (n8 <= 0) {
                        return Instruction::e_NOP_;
                      } else {
                        unsigned int n9 = n8 - 1;
                        if (n9 <= 0) {
                          return Instruction::e_NOP_;
                        } else {
                          unsigned int n10 = n9 - 1;
                          if (n10 <= 0) {
                            return Instruction::e_NOP_;
                          } else {
                            unsigned int n11 = n10 - 1;
                            if (n11 <= 0) {
                              return Instruction::e_NOP_;
                            } else {
                              unsigned int n12 = n11 - 1;
                              if (n12 <= 0) {
                                if (operand <= 0) {
                                  return Instruction::e_WRM_;
                                } else {
                                  unsigned int n13 = operand - 1;
                                  if (n13 <= 0) {
                                    return Instruction::e_NOP_;
                                  } else {
                                    unsigned int n14 = n13 - 1;
                                    if (n14 <= 0) {
                                      return Instruction::e_WRR_;
                                    } else {
                                      unsigned int n15 = n14 - 1;
                                      if (n15 <= 0) {
                                        return Instruction::e_NOP_;
                                      } else {
                                        unsigned int n16 = n15 - 1;
                                        if (n16 <= 0) {
                                          return Instruction::e_NOP_;
                                        } else {
                                          unsigned int n17 = n16 - 1;
                                          if (n17 <= 0) {
                                            return Instruction::e_NOP_;
                                          } else {
                                            unsigned int n18 = n17 - 1;
                                            if (n18 <= 0) {
                                              return Instruction::e_NOP_;
                                            } else {
                                              unsigned int n19 = n18 - 1;
                                              if (n19 <= 0) {
                                                return Instruction::e_NOP_;
                                              } else {
                                                unsigned int n20 = n19 - 1;
                                                if (n20 <= 0) {
                                                  return Instruction::e_NOP_;
                                                } else {
                                                  unsigned int n21 = n20 - 1;
                                                  if (n21 <= 0) {
                                                    return Instruction::e_RDM_;
                                                  } else {
                                                    unsigned int _x0 = n21 - 1;
                                                    return Instruction::e_NOP_;
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
                                unsigned int n13 = n12 - 1;
                                if (n13 <= 0) {
                                  if (operand <= 0) {
                                    return Instruction::e_NOP_;
                                  } else {
                                    unsigned int n14 = operand - 1;
                                    if (n14 <= 0) {
                                      return Instruction::e_NOP_;
                                    } else {
                                      unsigned int n15 = n14 - 1;
                                      if (n15 <= 0) {
                                        return Instruction::e_NOP_;
                                      } else {
                                        unsigned int n16 = n15 - 1;
                                        if (n16 <= 0) {
                                          return Instruction::e_NOP_;
                                        } else {
                                          unsigned int n17 = n16 - 1;
                                          if (n17 <= 0) {
                                            return Instruction::e_NOP_;
                                          } else {
                                            unsigned int n18 = n17 - 1;
                                            if (n18 <= 0) {
                                              return Instruction::e_NOP_;
                                            } else {
                                              unsigned int n19 = n18 - 1;
                                              if (n19 <= 0) {
                                                return Instruction::e_NOP_;
                                              } else {
                                                unsigned int n20 = n19 - 1;
                                                if (n20 <= 0) {
                                                  return Instruction::e_NOP_;
                                                } else {
                                                  unsigned int n21 = n20 - 1;
                                                  if (n21 <= 0) {
                                                    return Instruction::e_NOP_;
                                                  } else {
                                                    unsigned int n22 = n21 - 1;
                                                    if (n22 <= 0) {
                                                      return Instruction::
                                                          e_NOP_;
                                                    } else {
                                                      unsigned int n23 =
                                                          n22 - 1;
                                                      if (n23 <= 0) {
                                                        return Instruction::
                                                            e_NOP_;
                                                      } else {
                                                        unsigned int n24 =
                                                            n23 - 1;
                                                        if (n24 <= 0) {
                                                          return Instruction::
                                                              e_NOP_;
                                                        } else {
                                                          unsigned int n25 =
                                                              n24 - 1;
                                                          if (n25 <= 0) {
                                                            return Instruction::
                                                                e_NOP_;
                                                          } else {
                                                            unsigned int n26 =
                                                                n25 - 1;
                                                            if (n26 <= 0) {
                                                              return Instruction::
                                                                  e_DCL_;
                                                            } else {
                                                              unsigned int _x0 =
                                                                  n26 - 1;
                                                              return Instruction::
                                                                  e_NOP_;
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
                                  unsigned int _x0 = n13 - 1;
                                  return Instruction::e_NOP_;
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

__attribute__((pure)) std::pair<unsigned int, unsigned int>
Nat::divmod(const unsigned int x, const unsigned int y, const unsigned int q,
            const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return Nat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return Nat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

__attribute__((pure)) unsigned int Nat::div(const unsigned int x,
                                            const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
