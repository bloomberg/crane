#ifndef INCLUDED_PARSER_FRAME_MODTYPE_NIL
#define INCLUDED_PARSER_FRAME_MODTYPE_NIL

#include <any>
#include <cstdint>
#include <deque>
#include <type_traits>
#include <utility>
#include <variant>

/// Reproduces (now fixed) a compile-time failure in the extracted C++ parser
/// core that appeared after the grammar_pairlist_nil_cons_mismatch fix landed:
///
/// Parser.h: no viable conversion from
/// 'pair<Parser_frame, deque<any>>' to
/// 'pair<Parser_frame, deque<Parser_frame>>'
///
/// The real code (theories/Parser) is layered across TWO functors joined by an
/// ABSTRACT MODULE TYPE:
///
/// * theories/Parser/Defs.v defines parser_frame/parser_stack inside
/// Module DefsFn (Export Ty : SymbolTypes), then re-exposes DefsFn's
/// contents through a *module type*:
/// Module Type DefsT (SymTy : SymbolTypes). Include DefsFn SymTy. End DefsT.
/// Module Type T. Declare Module SymTy : SymbolTypes.
/// Declare Module Defs : DefsT SymTy. ... End T.
///
/// * theories/Parser/Parser.v defines the nil use-site inside a DIFFERENT
/// functor over that module type:
/// Module ParserFn (Import D : Defs.T).
/// Definition parse ... := let sk0 := (Fr  tt NT x, ) in ...
///
/// So at the literal outer [] (a list parser_frame nil), parser_frame is
/// seen *abstractly*, through the module type Defs.T -- NOT through the
/// concrete DefsFn output. That abstraction boundary is the essential
/// trigger: standalone / same-functor variants of this exact frame/stack shape
/// do NOT reproduce it (Crane emits std::deque<Frame>{} correctly). Only when
/// the nil use is behind the Include DefsFn-inside-a-Module Type boundary
/// does Crane's erasure collapse list frame's nil to the fully-erased shape
/// std::deque<std::any>{}, while frame's cons sites (in push_frame /
/// tail_lengths, reached from the concrete side) build/expect the concrete
/// std::deque<frame> shape -- a compile-time "no viable conversion" error.
///
/// Fix: the grammar_pairlist_nil_cons_mismatch hollow_container collapse (in
/// gen_expr_custom_cons) fired whenever the list's ML element annotation was
/// all-Tdummy, forcing the element to bare std::any.  It now additionally
/// requires the concrete C++ element type (temps) to be erased too.  Here the
/// abstract frame resolves to a fully-concrete typename D::Defs::frame
/// despite the hollow ML annotation, so the concrete std::deque<frame> shape
/// is preserved, while genuinely-erased lists (like the pairlist case) still
/// collapse to std::deque<std::any>.
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
