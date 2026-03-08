#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct LargeEnum {
  enum class color {
    Red,
    Orange,
    Yellow,
    Green,
    Blue,
    Indigo,
    Violet,
    Black,
    White,
    Gray,
    Brown,
    Pink
  };

  template <typename T1>
  static T1 color_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                       const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                       const T1 f7, const T1 f8, const T1 f9, const T1 f10,
                       const color c) {
    return [&](void) {
      switch (c) {
      case color::Red: {
        return f;
      }
      case color::Orange: {
        return f0;
      }
      case color::Yellow: {
        return f1;
      }
      case color::Green: {
        return f2;
      }
      case color::Blue: {
        return f3;
      }
      case color::Indigo: {
        return f4;
      }
      case color::Violet: {
        return f5;
      }
      case color::Black: {
        return f6;
      }
      case color::White: {
        return f7;
      }
      case color::Gray: {
        return f8;
      }
      case color::Brown: {
        return f9;
      }
      case color::Pink: {
        return f10;
      }
      }
    }();
  }

  template <typename T1>
  static T1 color_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                      const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                      const T1 f7, const T1 f8, const T1 f9, const T1 f10,
                      const color c) {
    return [&](void) {
      switch (c) {
      case color::Red: {
        return f;
      }
      case color::Orange: {
        return f0;
      }
      case color::Yellow: {
        return f1;
      }
      case color::Green: {
        return f2;
      }
      case color::Blue: {
        return f3;
      }
      case color::Indigo: {
        return f4;
      }
      case color::Violet: {
        return f5;
      }
      case color::Black: {
        return f6;
      }
      case color::White: {
        return f7;
      }
      case color::Gray: {
        return f8;
      }
      case color::Brown: {
        return f9;
      }
      case color::Pink: {
        return f10;
      }
      }
    }();
  }

  static unsigned int color_to_nat(const color c);

  static bool is_warm(const color c);

  static bool is_neutral(const color c);

  struct tok {
  public:
    struct TNum {
      unsigned int _a0;
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
      unsigned int _a0;
    };
    struct TEOF {};
    using variant_t =
        std::variant<TNum, TPlus, TMinus, TStar, TSlash, TLParen, TRParen, TEq,
                     TBang, TSemicolon, TIdent, TEOF>;

  private:
    variant_t v_;
    explicit tok(TNum _v) : v_(std::move(_v)) {}
    explicit tok(TPlus _v) : v_(std::move(_v)) {}
    explicit tok(TMinus _v) : v_(std::move(_v)) {}
    explicit tok(TStar _v) : v_(std::move(_v)) {}
    explicit tok(TSlash _v) : v_(std::move(_v)) {}
    explicit tok(TLParen _v) : v_(std::move(_v)) {}
    explicit tok(TRParen _v) : v_(std::move(_v)) {}
    explicit tok(TEq _v) : v_(std::move(_v)) {}
    explicit tok(TBang _v) : v_(std::move(_v)) {}
    explicit tok(TSemicolon _v) : v_(std::move(_v)) {}
    explicit tok(TIdent _v) : v_(std::move(_v)) {}
    explicit tok(TEOF _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<tok> TNum_(unsigned int a0) {
        return std::shared_ptr<tok>(new tok(TNum{a0}));
      }
      static std::shared_ptr<tok> TPlus_() {
        return std::shared_ptr<tok>(new tok(TPlus{}));
      }
      static std::shared_ptr<tok> TMinus_() {
        return std::shared_ptr<tok>(new tok(TMinus{}));
      }
      static std::shared_ptr<tok> TStar_() {
        return std::shared_ptr<tok>(new tok(TStar{}));
      }
      static std::shared_ptr<tok> TSlash_() {
        return std::shared_ptr<tok>(new tok(TSlash{}));
      }
      static std::shared_ptr<tok> TLParen_() {
        return std::shared_ptr<tok>(new tok(TLParen{}));
      }
      static std::shared_ptr<tok> TRParen_() {
        return std::shared_ptr<tok>(new tok(TRParen{}));
      }
      static std::shared_ptr<tok> TEq_() {
        return std::shared_ptr<tok>(new tok(TEq{}));
      }
      static std::shared_ptr<tok> TBang_() {
        return std::shared_ptr<tok>(new tok(TBang{}));
      }
      static std::shared_ptr<tok> TSemicolon_() {
        return std::shared_ptr<tok>(new tok(TSemicolon{}));
      }
      static std::shared_ptr<tok> TIdent_(unsigned int a0) {
        return std::shared_ptr<tok>(new tok(TIdent{a0}));
      }
      static std::shared_ptr<tok> TEOF_() {
        return std::shared_ptr<tok>(new tok(TEOF{}));
      }
      static std::unique_ptr<tok> TNum_uptr(unsigned int a0) {
        return std::unique_ptr<tok>(new tok(TNum{a0}));
      }
      static std::unique_ptr<tok> TPlus_uptr() {
        return std::unique_ptr<tok>(new tok(TPlus{}));
      }
      static std::unique_ptr<tok> TMinus_uptr() {
        return std::unique_ptr<tok>(new tok(TMinus{}));
      }
      static std::unique_ptr<tok> TStar_uptr() {
        return std::unique_ptr<tok>(new tok(TStar{}));
      }
      static std::unique_ptr<tok> TSlash_uptr() {
        return std::unique_ptr<tok>(new tok(TSlash{}));
      }
      static std::unique_ptr<tok> TLParen_uptr() {
        return std::unique_ptr<tok>(new tok(TLParen{}));
      }
      static std::unique_ptr<tok> TRParen_uptr() {
        return std::unique_ptr<tok>(new tok(TRParen{}));
      }
      static std::unique_ptr<tok> TEq_uptr() {
        return std::unique_ptr<tok>(new tok(TEq{}));
      }
      static std::unique_ptr<tok> TBang_uptr() {
        return std::unique_ptr<tok>(new tok(TBang{}));
      }
      static std::unique_ptr<tok> TSemicolon_uptr() {
        return std::unique_ptr<tok>(new tok(TSemicolon{}));
      }
      static std::unique_ptr<tok> TIdent_uptr(unsigned int a0) {
        return std::unique_ptr<tok>(new tok(TIdent{a0}));
      }
      static std::unique_ptr<tok> TEOF_uptr() {
        return std::unique_ptr<tok>(new tok(TEOF{}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F10>
  static T1 tok_rect(F0 &&f, const T1 f0, const T1 f1, const T1 f2, const T1 f3,
                     const T1 f4, const T1 f5, const T1 f6, const T1 f7,
                     const T1 f8, F10 &&f9, const T1 f10,
                     const std::shared_ptr<tok> &t) {
    return std::visit(
        Overloaded{
            [&](const typename tok::TNum _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
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
              unsigned int n = _args._a0;
              return f9(std::move(n));
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
            [&](const typename tok::TNum _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
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
              unsigned int n = _args._a0;
              return f9(std::move(n));
            },
            [&](const typename tok::TEOF _args) -> T1 { return f10; }},
        t->v());
  }

  static unsigned int tok_to_nat(const std::shared_ptr<tok> &t);

  static bool is_operator(const std::shared_ptr<tok> &t);

  static inline const unsigned int test_red = color_to_nat(color::Red);

  static inline const unsigned int test_pink = color_to_nat(color::Pink);

  static inline const bool test_warm_red = is_warm(color::Red);

  static inline const bool test_warm_blue = is_warm(color::Blue);

  static inline const bool test_neutral_black = is_neutral(color::Black);

  static inline const bool test_neutral_red = is_neutral(color::Red);

  static inline const unsigned int test_tok_num =
      tok_to_nat(tok::ctor::TNum_(42u));

  static inline const unsigned int test_tok_plus =
      tok_to_nat(tok::ctor::TPlus_());

  static inline const unsigned int test_tok_ident =
      tok_to_nat(tok::ctor::TIdent_(3u));

  static inline const unsigned int test_tok_eof =
      tok_to_nat(tok::ctor::TEOF_());

  static inline const bool test_is_op_plus = is_operator(tok::ctor::TPlus_());

  static inline const bool test_is_op_num = is_operator(tok::ctor::TNum_(0u));
};
