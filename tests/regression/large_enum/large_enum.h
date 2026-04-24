#ifndef INCLUDED_LARGE_ENUM
#define INCLUDED_LARGE_ENUM

#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

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
    tok() {}

    explicit tok(TNum _v) : d_v_(std::move(_v)) {}

    explicit tok(TPlus _v) : d_v_(_v) {}

    explicit tok(TMinus _v) : d_v_(_v) {}

    explicit tok(TStar _v) : d_v_(_v) {}

    explicit tok(TSlash _v) : d_v_(_v) {}

    explicit tok(TLParen _v) : d_v_(_v) {}

    explicit tok(TRParen _v) : d_v_(_v) {}

    explicit tok(TEq _v) : d_v_(_v) {}

    explicit tok(TBang _v) : d_v_(_v) {}

    explicit tok(TSemicolon _v) : d_v_(_v) {}

    explicit tok(TIdent _v) : d_v_(std::move(_v)) {}

    explicit tok(TEOF _v) : d_v_(_v) {}

    tok(const tok &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tok(tok &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) tok &operator=(const tok &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) tok &operator=(tok &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tok clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<TNum>(_sv.v())) {
        const auto &[d_a0] = std::get<TNum>(_sv.v());
        return tok(TNum{clone_as_value<unsigned int>(d_a0)});
      } else if (std::holds_alternative<TPlus>(_sv.v())) {
        return tok(TPlus{});
      } else if (std::holds_alternative<TMinus>(_sv.v())) {
        return tok(TMinus{});
      } else if (std::holds_alternative<TStar>(_sv.v())) {
        return tok(TStar{});
      } else if (std::holds_alternative<TSlash>(_sv.v())) {
        return tok(TSlash{});
      } else if (std::holds_alternative<TLParen>(_sv.v())) {
        return tok(TLParen{});
      } else if (std::holds_alternative<TRParen>(_sv.v())) {
        return tok(TRParen{});
      } else if (std::holds_alternative<TEq>(_sv.v())) {
        return tok(TEq{});
      } else if (std::holds_alternative<TBang>(_sv.v())) {
        return tok(TBang{});
      } else if (std::holds_alternative<TSemicolon>(_sv.v())) {
        return tok(TSemicolon{});
      } else if (std::holds_alternative<TIdent>(_sv.v())) {
        const auto &[d_a0] = std::get<TIdent>(_sv.v());
        return tok(TIdent{clone_as_value<unsigned int>(d_a0)});
      } else {
        return tok(TEOF{});
      }
    }

    // CREATORS
    __attribute__((pure)) static tok tnum(unsigned int a0) {
      return tok(TNum{std::move(a0)});
    }

    constexpr static tok tplus() { return tok(TPlus{}); }

    constexpr static tok tminus() { return tok(TMinus{}); }

    constexpr static tok tstar() { return tok(TStar{}); }

    constexpr static tok tslash() { return tok(TSlash{}); }

    constexpr static tok tlparen() { return tok(TLParen{}); }

    constexpr static tok trparen() { return tok(TRParen{}); }

    constexpr static tok teq() { return tok(TEq{}); }

    constexpr static tok tbang() { return tok(TBang{}); }

    constexpr static tok tsemicolon() { return tok(TSemicolon{}); }

    __attribute__((pure)) static tok tident(unsigned int a0) {
      return tok(TIdent{std::move(a0)});
    }

    constexpr static tok teof() { return tok(TEOF{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tok *operator->() { return this; }

    __attribute__((pure)) const tok *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tok(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F10>
  static T1 tok_rect(F0 &&f, const T1 f0, const T1 f1, const T1 f2, const T1 f3,
                     const T1 f4, const T1 f5, const T1 f6, const T1 f7,
                     const T1 f8, F10 &&f9, const T1 f10, const tok &t) {
    if (std::holds_alternative<typename tok::TNum>(t.v())) {
      const auto &[d_a0] = std::get<typename tok::TNum>(t.v());
      return f(d_a0);
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
      const auto &[d_a0] = std::get<typename tok::TIdent>(t.v());
      return f9(d_a0);
    } else {
      return f10;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F10>
  static T1 tok_rec(F0 &&f, const T1 f0, const T1 f1, const T1 f2, const T1 f3,
                    const T1 f4, const T1 f5, const T1 f6, const T1 f7,
                    const T1 f8, F10 &&f9, const T1 f10, const tok &t) {
    if (std::holds_alternative<typename tok::TNum>(t.v())) {
      const auto &[d_a0] = std::get<typename tok::TNum>(t.v());
      return f(d_a0);
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
      const auto &[d_a0] = std::get<typename tok::TIdent>(t.v());
      return f9(d_a0);
    } else {
      return f10;
    }
  }

  __attribute__((pure)) static unsigned int tok_to_nat(const tok &t);
  __attribute__((pure)) static bool is_operator(const tok &t);
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
