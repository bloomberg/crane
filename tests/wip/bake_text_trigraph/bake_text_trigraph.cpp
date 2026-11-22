#include "bake_text_trigraph.h"

Positive Pos::pred_double(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return Positive::xi(Positive::xo(crane::shared_child(a0)));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return Positive::xi(pred_double(*a0));
  } else {
    return Positive::xh();
  }
}

uint64_t Pos::to_nat(const Positive &x) {
  return iter_op<uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); }, x,
      UINT64_C(1));
}

Z IntDef::double_(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zpos(Positive::xo(a0));
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zneg(Positive::xo(a0));
  }
}

Z IntDef::succ_double(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::zpos(Positive::xh());
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zpos(Positive::xi(a0));
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zneg(Pos::pred_double(a0));
  }
}

uint64_t BinInt::to_nat(const Z &z) {
  if (std::holds_alternative<typename Z::Zpos>(z.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(z.v());
    return Pos::to_nat(a0);
  } else {
    return UINT64_C(0);
  }
}

bool Uint63Axioms::is_zero(int64_t i) { return i == INT64_C(0); }

bool Uint63Axioms::is_even(int64_t i) {
  return Uint63Axioms::is_zero((i & INT64_C(1)));
}

Z Uint63Axioms::to_Z_rec(uint64_t n, int64_t i) {
  if (n <= 0) {
    return Z::z0();
  } else {
    uint64_t n0 = n - 1;
    if (Uint63Axioms::is_even(i)) {
      return IntDef::double_(Uint63Axioms::to_Z_rec(
          n0, (INT64_C(1) >= 63
                   ? 0
                   : static_cast<int64_t>(
                         static_cast<uint64_t>(i) >> (INT64_C(1) & 63)))));
    } else {
      return IntDef::succ_double(Uint63Axioms::to_Z_rec(
          n0, (INT64_C(1) >= 63
                   ? 0
                   : static_cast<int64_t>(
                         static_cast<uint64_t>(i) >> (INT64_C(1) & 63)))));
    }
  }
}

Z Uint63Axioms::to_Z(int64_t x0_) {
  return Uint63Axioms::to_Z_rec(Uint63Axioms::size, x0_);
}

// Baked by crane::bake: the value of crane_baked_words_0efe2e38af3c.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const char crane_baked_words_0efe2e38af3c_text[] = "??" "a" "??=";
constinit const std::uint64_t crane_baked_words_0efe2e38af3c_words[] = {
    1, 4,     // List<std::string>: #0 to #3
    0,        // #0 Nil
    1, 2, 0,  // #1 Cons{a = "??", l = #0}
    1, 1, 1,  // #2 Cons{a = "a", l = #1}
    1, 3, 2,  // #3 Cons{a = "??=", l = #2}
    0,        // end of the nodes
    3,        // the value: #3
};
constinit const crane::bake::image crane_baked_words_0efe2e38af3c{
    crane_baked_words_0efe2e38af3c_words, 14, nullptr, 0,
    crane_baked_words_0efe2e38af3c_text, 6};
