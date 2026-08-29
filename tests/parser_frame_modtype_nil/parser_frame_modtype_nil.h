#ifndef INCLUDED_PARSER_FRAME_MODTYPE_NIL
#define INCLUDED_PARSER_FRAME_MODTYPE_NIL

#include <any>
#include <cstdint>
#include <deque>
#include <type_traits>
#include <utility>
#include <variant>

using tuple = std::any;
template <typename M>
concept SymbolTypes = requires {
  typename M::symbol;
  typename M::symbol_semty;
};

template <SymbolTypes Ty> struct DefsFn {
  using symbols_semty = tuple;

  struct frame {
    // DATA
    std::deque<typename Ty::symbol> pre;
    symbols_semty sem;
    std::deque<typename Ty::symbol> suf;

    // ACCESSORS
    frame clone() const { return {pre, sem, suf}; }

    // CREATORS
    static frame fr(std::deque<typename Ty::symbol> pre, symbols_semty sem,
                    std::deque<typename Ty::symbol> suf) {
      return {std::move(pre), std::move(sem), std::move(suf)};
    }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, std::deque<typename Ty::symbol> &,
                                   symbols_semty &,
                                   std::deque<typename Ty::symbol> &>
  static T1 frame_rect(F0 &&f, const frame &f0) {
    const auto &[pre0, sem0, suf0] = f0;
    return f(pre0, sem0, suf0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, std::deque<typename Ty::symbol> &,
                                   symbols_semty &,
                                   std::deque<typename Ty::symbol> &>
  static T1 frame_rec(F0 &&f, const frame &f0) {
    const auto &[pre0, sem0, suf0] = f0;
    return f(pre0, sem0, suf0);
  }

  using stack = std::pair<frame, std::deque<frame>>;

  static stack push_frame(frame f, std::pair<frame, std::deque<frame>> s) {
    auto [top, rest] = std::move(s);
    return std::make_pair(std::move(f), [](auto _a0, auto _a1) {
      _a1.push_front(_a0);
      return _a1;
    }(std::move(top), rest));
  }

  static uint64_t tail_lengths(const std::deque<frame> &frs) {
    if (frs.empty()) {
      return UINT64_C(0);
    } else {
      const auto &f = frs.front();
      std::decay_t<decltype(frs)> frs_(frs.begin() + 1, frs.end());
      const auto &[pre, sem, suf0] = f;
      return (static_cast<uint64_t>(suf0.size()) + tail_lengths(frs_));
    }
  }
};

template <typename M>
concept T = requires { requires SymbolTypes<typename M::SymTy>; };

template <T D> struct ParserFn {
  static uint64_t
  step_stack(const std::pair<typename D::Defs::frame,
                             std::deque<typename D::Defs::frame>> &s) {
    const auto &[f, frs] = s;
    const auto &[pre, sem, suf0] = f;
    return (static_cast<uint64_t>(suf0.size()) + D::Defs::tail_lengths(frs));
  }

  static uint64_t parse(typename D::SymTy::symbol x) {
    auto sk0 = std::make_pair(
        D::Defs::frame::fr(std::deque<typename D::SymTy::symbol>{},
                           std::monostate{},
                           [](auto _a0, auto _a1) {
                             _a1.push_front(_a0);
                             return _a1;
                           }(x, std::deque<typename D::SymTy::symbol>{})),
        std::deque<typename D::Defs::frame>{});
    return step_stack(std::move(sk0));
  }
};
enum class Concrete_symbol { SA, SB };
using concrete_symbol_semty = std::any;

struct ConcreteSymTypes {
  using symbol = Concrete_symbol;
  using symbol_semty = concrete_symbol_semty;
};

struct D {
  using SymTy = ConcreteSymTypes;
  using Defs = DefsFn<SymTy>;
};

using TheParser = ParserFn<D>;

#endif // INCLUDED_PARSER_FRAME_MODTYPE_NIL
