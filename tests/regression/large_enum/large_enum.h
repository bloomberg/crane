#ifndef INCLUDED_LARGE_ENUM
#define INCLUDED_LARGE_ENUM

#include <type_traits>
#include <utility>
#include <variant>

struct LargeEnum {
  enum class Color {
    RED,
    ORANGE,
    YELLOW,
    GREEN,
    BLUE,
    INDIGO,
    VIOLET,
    BLACK,
    WHITE,
    GRAY,
    BROWN,
    PINK
  };

  template <typename T1>
  static T1 color_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5, T1 f6,
                       T1 f7, T1 f8, T1 f9, T1 f10, Color c) {
    switch (c) {
    case Color::RED: {
      return f;
    } break;
    case Color::ORANGE: {
      return f0;
    } break;
    case Color::YELLOW: {
      return f1;
    } break;
    case Color::GREEN: {
      return f2;
    } break;
    case Color::BLUE: {
      return f3;
    } break;
    case Color::INDIGO: {
      return f4;
    } break;
    case Color::VIOLET: {
      return f5;
    } break;
    case Color::BLACK: {
      return f6;
    } break;
    case Color::WHITE: {
      return f7;
    } break;
    case Color::GRAY: {
      return f8;
    } break;
    case Color::BROWN: {
      return f9;
    } break;
    case Color::PINK: {
      return f10;
    } break;
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 color_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5, T1 f6,
                      T1 f7, T1 f8, T1 f9, T1 f10, Color c) {
    switch (c) {
    case Color::RED: {
      return f;
    } break;
    case Color::ORANGE: {
      return f0;
    } break;
    case Color::YELLOW: {
      return f1;
    } break;
    case Color::GREEN: {
      return f2;
    } break;
    case Color::BLUE: {
      return f3;
    } break;
    case Color::INDIGO: {
      return f4;
    } break;
    case Color::VIOLET: {
      return f5;
    } break;
    case Color::BLACK: {
      return f6;
    } break;
    case Color::WHITE: {
      return f7;
    } break;
    case Color::GRAY: {
      return f8;
    } break;
    case Color::BROWN: {
      return f9;
    } break;
    case Color::PINK: {
      return f10;
    } break;
    default:
      std::unreachable();
    }
  }

  static uint64_t color_to_nat(Color c);
  static bool is_warm(Color c);
  static bool is_neutral(Color c);

  struct tok {
    // TYPES
    struct TNum {
      uint64_t a0;
    };

    struct TPlus {};

    struct TMinus {};

    struct TStar {};

    struct TSlash {};

    struct TLParen {};

    struct TRParen {};

    struct TEq {};

    struct TBang {};

    struct TSemicolon {};

    struct TIdent {
      uint64_t a0;
    };

    struct TEOF {};

    using variant_t =
        std::variant<TNum, TPlus, TMinus, TStar, TSlash, TLParen, TRParen, TEq,
                     TBang, TSemicolon, TIdent, TEOF>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tok() {}

    explicit tok(TNum _v) : v_(std::move(_v)) {}

    explicit tok(TPlus _v) : v_(_v) {}

    explicit tok(TMinus _v) : v_(_v) {}

    explicit tok(TStar _v) : v_(_v) {}

    explicit tok(TSlash _v) : v_(_v) {}

    explicit tok(TLParen _v) : v_(_v) {}

    explicit tok(TRParen _v) : v_(_v) {}

    explicit tok(TEq _v) : v_(_v) {}

    explicit tok(TBang _v) : v_(_v) {}

    explicit tok(TSemicolon _v) : v_(_v) {}

    explicit tok(TIdent _v) : v_(std::move(_v)) {}

    explicit tok(TEOF _v) : v_(_v) {}

    static tok tnum(uint64_t a0) { return tok(TNum{a0}); }

    static tok tplus() { return tok(TPlus{}); }

    static tok tminus() { return tok(TMinus{}); }

    static tok tstar() { return tok(TStar{}); }

    static tok tslash() { return tok(TSlash{}); }

    static tok tlparen() { return tok(TLParen{}); }

    static tok trparen() { return tok(TRParen{}); }

    static tok teq() { return tok(TEq{}); }

    static tok tbang() { return tok(TBang{}); }

    static tok tsemicolon() { return tok(TSemicolon{}); }

    static tok tident(uint64_t a0) { return tok(TIdent{a0}); }

    static tok teof() { return tok(TEOF{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F10>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F10 &, uint64_t &>
  static T1 tok_rect(F0 &&f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5, T1 f6,
                     T1 f7, T1 f8, F10 &&f9, T1 f10, const tok &t) {
    if (std::holds_alternative<typename tok::TNum>(t.v())) {
      const auto &[a0] = std::get<typename tok::TNum>(t.v());
      return f(a0);
    } else if (std::holds_alternative<typename tok::TPlus>(t.v())) {
      return f0;
    } else if (std::holds_alternative<typename tok::TMinus>(t.v())) {
      return f1;
    } else if (std::holds_alternative<typename tok::TStar>(t.v())) {
      return f2;
    } else if (std::holds_alternative<typename tok::TSlash>(t.v())) {
      return f3;
    } else if (std::holds_alternative<typename tok::TLParen>(t.v())) {
      return f4;
    } else if (std::holds_alternative<typename tok::TRParen>(t.v())) {
      return f5;
    } else if (std::holds_alternative<typename tok::TEq>(t.v())) {
      return f6;
    } else if (std::holds_alternative<typename tok::TBang>(t.v())) {
      return f7;
    } else if (std::holds_alternative<typename tok::TSemicolon>(t.v())) {
      return f8;
    } else if (std::holds_alternative<typename tok::TIdent>(t.v())) {
      const auto &[a0] = std::get<typename tok::TIdent>(t.v());
      return f9(a0);
    } else {
      return f10;
    }
  }

  template <typename T1, typename F0, typename F10>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F10 &, uint64_t &>
  static T1 tok_rec(F0 &&f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5, T1 f6,
                    T1 f7, T1 f8, F10 &&f9, T1 f10, const tok &t) {
    if (std::holds_alternative<typename tok::TNum>(t.v())) {
      const auto &[a0] = std::get<typename tok::TNum>(t.v());
      return f(a0);
    } else if (std::holds_alternative<typename tok::TPlus>(t.v())) {
      return f0;
    } else if (std::holds_alternative<typename tok::TMinus>(t.v())) {
      return f1;
    } else if (std::holds_alternative<typename tok::TStar>(t.v())) {
      return f2;
    } else if (std::holds_alternative<typename tok::TSlash>(t.v())) {
      return f3;
    } else if (std::holds_alternative<typename tok::TLParen>(t.v())) {
      return f4;
    } else if (std::holds_alternative<typename tok::TRParen>(t.v())) {
      return f5;
    } else if (std::holds_alternative<typename tok::TEq>(t.v())) {
      return f6;
    } else if (std::holds_alternative<typename tok::TBang>(t.v())) {
      return f7;
    } else if (std::holds_alternative<typename tok::TSemicolon>(t.v())) {
      return f8;
    } else if (std::holds_alternative<typename tok::TIdent>(t.v())) {
      const auto &[a0] = std::get<typename tok::TIdent>(t.v());
      return f9(a0);
    } else {
      return f10;
    }
  }

  static uint64_t tok_to_nat(const tok &t);
  static bool is_operator(const tok &t);
  static inline const uint64_t test_red = color_to_nat(Color::RED);
  static inline const uint64_t test_pink = color_to_nat(Color::PINK);
  static inline const bool test_warm_red = is_warm(Color::RED);
  static inline const bool test_warm_blue = is_warm(Color::BLUE);
  static inline const bool test_neutral_black = is_neutral(Color::BLACK);
  static inline const bool test_neutral_red = is_neutral(Color::RED);
  static inline const uint64_t test_tok_num =
      tok_to_nat(tok::tnum(UINT64_C(42)));
  static inline const uint64_t test_tok_plus = tok_to_nat(tok::tplus());
  static inline const uint64_t test_tok_ident =
      tok_to_nat(tok::tident(UINT64_C(3)));
  static inline const uint64_t test_tok_eof = tok_to_nat(tok::teof());
  static inline const bool test_is_op_plus = is_operator(tok::tplus());
  static inline const bool test_is_op_num = is_operator(tok::tnum(UINT64_C(0)));
};

#endif // INCLUDED_LARGE_ENUM
