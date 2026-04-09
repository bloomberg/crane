#ifndef INCLUDED_LARGE_ENUM
#define INCLUDED_LARGE_ENUM

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct LargeEnum {
  enum class Color {
    e_RED,
    e_ORANGE,
    e_YELLOW,
    e_GREEN,
    e_BLUE,
    e_INDIGO,
    e_VIOLET,
    e_BLACK,
    e_WHITE,
    e_GRAY,
    e_BROWN,
    e_PINK
  };

  template <typename T1>
  static T1 color_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                       const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                       const T1 f7, const T1 f8, const T1 f9, const T1 f10,
                       const Color c) {
    switch (c) {
    case Color::e_RED: {
      return f;
    }
    case Color::e_ORANGE: {
      return f0;
    }
    case Color::e_YELLOW: {
      return f1;
    }
    case Color::e_GREEN: {
      return f2;
    }
    case Color::e_BLUE: {
      return f3;
    }
    case Color::e_INDIGO: {
      return f4;
    }
    case Color::e_VIOLET: {
      return f5;
    }
    case Color::e_BLACK: {
      return f6;
    }
    case Color::e_WHITE: {
      return f7;
    }
    case Color::e_GRAY: {
      return f8;
    }
    case Color::e_BROWN: {
      return f9;
    }
    case Color::e_PINK: {
      return f10;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 color_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                      const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                      const T1 f7, const T1 f8, const T1 f9, const T1 f10,
                      const Color c) {
    switch (c) {
    case Color::e_RED: {
      return f;
    }
    case Color::e_ORANGE: {
      return f0;
    }
    case Color::e_YELLOW: {
      return f1;
    }
    case Color::e_GREEN: {
      return f2;
    }
    case Color::e_BLUE: {
      return f3;
    }
    case Color::e_INDIGO: {
      return f4;
    }
    case Color::e_VIOLET: {
      return f5;
    }
    case Color::e_BLACK: {
      return f6;
    }
    case Color::e_WHITE: {
      return f7;
    }
    case Color::e_GRAY: {
      return f8;
    }
    case Color::e_BROWN: {
      return f9;
    }
    case Color::e_PINK: {
      return f10;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int color_to_nat(const Color c);
  __attribute__((pure)) static bool is_warm(const Color c);
  __attribute__((pure)) static bool is_neutral(const Color c);

  struct tok {
    // TYPES
    struct TNum {
      unsigned int d_a0;
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
      unsigned int d_a0;
    };

    struct TEOF {};

    using variant_t =
        std::variant<TNum, TPlus, TMinus, TStar, TSlash, TLParen, TRParen, TEq,
                     TBang, TSemicolon, TIdent, TEOF>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tok(TNum _v) : d_v_(std::move(_v)) {}

    explicit tok(TPlus _v) : d_v_(std::move(_v)) {}

    explicit tok(TMinus _v) : d_v_(std::move(_v)) {}

    explicit tok(TStar _v) : d_v_(std::move(_v)) {}

    explicit tok(TSlash _v) : d_v_(std::move(_v)) {}

    explicit tok(TLParen _v) : d_v_(std::move(_v)) {}

    explicit tok(TRParen _v) : d_v_(std::move(_v)) {}

    explicit tok(TEq _v) : d_v_(std::move(_v)) {}

    explicit tok(TBang _v) : d_v_(std::move(_v)) {}

    explicit tok(TSemicolon _v) : d_v_(std::move(_v)) {}

    explicit tok(TIdent _v) : d_v_(std::move(_v)) {}

    explicit tok(TEOF _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tok> tnum(unsigned int a0) {
      return std::make_shared<tok>(TNum{std::move(a0)});
    }

    static std::shared_ptr<tok> tplus() {
      return std::make_shared<tok>(TPlus{});
    }

    static std::shared_ptr<tok> tminus() {
      return std::make_shared<tok>(TMinus{});
    }

    static std::shared_ptr<tok> tstar() {
      return std::make_shared<tok>(TStar{});
    }

    static std::shared_ptr<tok> tslash() {
      return std::make_shared<tok>(TSlash{});
    }

    static std::shared_ptr<tok> tlparen() {
      return std::make_shared<tok>(TLParen{});
    }

    static std::shared_ptr<tok> trparen() {
      return std::make_shared<tok>(TRParen{});
    }

    static std::shared_ptr<tok> teq() { return std::make_shared<tok>(TEq{}); }

    static std::shared_ptr<tok> tbang() {
      return std::make_shared<tok>(TBang{});
    }

    static std::shared_ptr<tok> tsemicolon() {
      return std::make_shared<tok>(TSemicolon{});
    }

    static std::shared_ptr<tok> tident(unsigned int a0) {
      return std::make_shared<tok>(TIdent{std::move(a0)});
    }

    static std::shared_ptr<tok> teof() { return std::make_shared<tok>(TEOF{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F10>
  static T1 tok_rect(F0 &&f, const T1 f0, const T1 f1, const T1 f2, const T1 f3,
                     const T1 f4, const T1 f5, const T1 f6, const T1 f7,
                     const T1 f8, F10 &&f9, const T1 f10,
                     const std::shared_ptr<tok> &t) {
    return std::visit(
        Overloaded{
            [&](const typename tok::TNum _args) -> T1 { return f(_args.d_a0); },
            [&](const typename tok::TPlus _args) -> T1 { return f0; },
            [&](const typename tok::TMinus _args) -> T1 { return f1; },
            [&](const typename tok::TStar _args) -> T1 { return f2; },
            [&](const typename tok::TSlash _args) -> T1 { return f3; },
            [&](const typename tok::TLParen _args) -> T1 { return f4; },
            [&](const typename tok::TRParen _args) -> T1 { return f5; },
            [&](const typename tok::TEq _args) -> T1 { return f6; },
            [&](const typename tok::TBang _args) -> T1 { return f7; },
            [&](const typename tok::TSemicolon _args) -> T1 { return f8; },
            [&](const typename tok::TIdent _args) -> T1 {
              return f9(_args.d_a0);
            },
            [&](const typename tok::TEOF _args) -> T1 { return f10; }},
        t->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F10>
  static T1 tok_rec(F0 &&f, const T1 f0, const T1 f1, const T1 f2, const T1 f3,
                    const T1 f4, const T1 f5, const T1 f6, const T1 f7,
                    const T1 f8, F10 &&f9, const T1 f10,
                    const std::shared_ptr<tok> &t) {
    return std::visit(
        Overloaded{
            [&](const typename tok::TNum _args) -> T1 { return f(_args.d_a0); },
            [&](const typename tok::TPlus _args) -> T1 { return f0; },
            [&](const typename tok::TMinus _args) -> T1 { return f1; },
            [&](const typename tok::TStar _args) -> T1 { return f2; },
            [&](const typename tok::TSlash _args) -> T1 { return f3; },
            [&](const typename tok::TLParen _args) -> T1 { return f4; },
            [&](const typename tok::TRParen _args) -> T1 { return f5; },
            [&](const typename tok::TEq _args) -> T1 { return f6; },
            [&](const typename tok::TBang _args) -> T1 { return f7; },
            [&](const typename tok::TSemicolon _args) -> T1 { return f8; },
            [&](const typename tok::TIdent _args) -> T1 {
              return f9(_args.d_a0);
            },
            [&](const typename tok::TEOF _args) -> T1 { return f10; }},
        t->v());
  }

  __attribute__((pure)) static unsigned int
  tok_to_nat(const std::shared_ptr<tok> &t);
  __attribute__((pure)) static bool is_operator(const std::shared_ptr<tok> &t);
  static inline const unsigned int test_red = color_to_nat(Color::e_RED);
  static inline const unsigned int test_pink = color_to_nat(Color::e_PINK);
  static inline const bool test_warm_red = is_warm(Color::e_RED);
  static inline const bool test_warm_blue = is_warm(Color::e_BLUE);
  static inline const bool test_neutral_black = is_neutral(Color::e_BLACK);
  static inline const bool test_neutral_red = is_neutral(Color::e_RED);
  static inline const unsigned int test_tok_num = tok_to_nat(tok::tnum(42u));
  static inline const unsigned int test_tok_plus = tok_to_nat(tok::tplus());
  static inline const unsigned int test_tok_ident = tok_to_nat(tok::tident(3u));
  static inline const unsigned int test_tok_eof = tok_to_nat(tok::teof());
  static inline const bool test_is_op_plus = is_operator(tok::tplus());
  static inline const bool test_is_op_num = is_operator(tok::tnum(0u));
};

#endif // INCLUDED_LARGE_ENUM
