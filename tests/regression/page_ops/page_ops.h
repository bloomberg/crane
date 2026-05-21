#ifndef INCLUDED_PAGE_OPS
#define INCLUDED_PAGE_OPS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_shared<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Nat {
  static uint64_t pow(uint64_t n, uint64_t m);
};

struct PageOps {
  struct state {
    uint64_t pc;

    // ACCESSORS
    state clone() const { return state{this->pc}; }
  };

  static uint64_t addr12_of_nat(uint64_t n);
  static uint64_t page_of(uint64_t p);
  static uint64_t page_base(uint64_t p);
  static uint64_t page_offset(uint64_t p);
  static uint64_t pc_inc1(const state &s);
  static uint64_t pc_inc2(const state &s);
  static uint64_t base_for_next1(const state &s);
  static uint64_t base_for_next2(const state &s);
  static uint64_t recompose(uint64_t p);
  static inline const uint64_t max_addr =
      (((Nat::pow(UINT64_C(2), UINT64_C(12)) - UINT64_C(1)) >
                Nat::pow(UINT64_C(2), UINT64_C(12))
            ? 0
            : (Nat::pow(UINT64_C(2), UINT64_C(12)) - UINT64_C(1))));

  struct instruction {
    // TYPES
    struct NOP {};

    struct LDM {
      uint64_t a0;
    };

    using variant_t = std::variant<NOP, LDM>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instruction() {}

    explicit instruction(NOP _v) : v_(_v) {}

    explicit instruction(LDM _v) : v_(std::move(_v)) {}

    instruction(const instruction &_other) : v_(std::move(_other.clone().v_)) {}

    instruction(instruction &&_other) noexcept : v_(std::move(_other.v_)) {}

    instruction &operator=(const instruction &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    instruction &operator=(instruction &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    instruction clone() const {
      if (std::holds_alternative<NOP>(this->v())) {
        return instruction(NOP{});
      } else {
        const auto &[a0] = std::get<LDM>(this->v());
        return instruction(LDM{a0});
      }
    }

    // CREATORS
    static instruction nop() { return instruction(NOP{}); }

    static instruction ldm(uint64_t a0) { return instruction(LDM{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 instruction_rect(T1 f, F1 &&f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename instruction::LDM>(i.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 instruction_rec(T1 f, F1 &&f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename instruction::LDM>(i.v());
      return f0(a0);
    }
  }

  static instruction decode(uint64_t b1, uint64_t b2);

  template <typename T1> static List<T1> drop(uint64_t n, List<T1> l) {
    if (n <= 0) {
      return l;
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v_mut())) {
        return List<T1>::nil();
      } else {
        auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v_mut());
        return drop<T1>(n_, *a1);
      }
    }
  }

  static std::optional<std::pair<instruction, uint64_t>>
  disassemble(const List<uint64_t> &rom, uint64_t addr);
  static inline const uint64_t test_page_base_alignment =
      (UINT64_C(256) ? page_base(UINT64_C(777)) % UINT64_C(256)
                     : page_base(UINT64_C(777)));
  static inline const uint64_t test_page_base_next_pc = []() {
    state s = state{UINT64_C(511)};
    return (base_for_next1(s) + base_for_next2(s));
  }();
  static inline const uint64_t test_page_boundary_cross =
      base_for_next1(state{UINT64_C(255)});
  static inline const uint64_t test_base_for_next_page_cross_1 =
      base_for_next1(state{UINT64_C(255)});
  static inline const uint64_t test_base_for_next_page_cross_2 =
      base_for_next2(state{UINT64_C(255)});
  static inline const bool test_page_decomp_roundtrip =
      (((UINT64_C(256) ? UINT64_C(1027) / UINT64_C(256) : 0) * UINT64_C(256)) +
       (UINT64_C(256) ? UINT64_C(1027) % UINT64_C(256) : UINT64_C(1027))) ==
      UINT64_C(1027);
  static inline const uint64_t test_page_offset_recompose =
      recompose(addr12_of_nat(UINT64_C(1027)));
  static inline const uint64_t test_page_recompose =
      recompose(addr12_of_nat(UINT64_C(1027)));
  static inline const uint64_t test_pc_inc2_wraparound =
      pc_inc2(state{max_addr});
  static inline const uint64_t test_pc_inc1_wrap = pc_inc1(state{max_addr});
  static inline const uint64_t test_pc_inc2_wrap = pc_inc2(state{max_addr});
  static inline const uint64_t test_disassemble_edge = []() -> uint64_t {
    auto _cs = disassemble(
        List<uint64_t>::cons(
            UINT64_C(0),
            List<uint64_t>::cons(
                UINT64_C(7),
                List<uint64_t>::cons(
                    UINT64_C(9), List<uint64_t>::cons(UINT64_C(11),
                                                      List<uint64_t>::nil())))),
        UINT64_C(0));
    if (_cs.has_value()) {
      const std::pair<instruction, uint64_t> &p = *_cs;
      const instruction &_x = p.first;
      const uint64_t &next = p.second;
      return next;
    } else {
      return UINT64_C(0);
    }
  }();
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<
                          std::pair<
                              std::pair<std::pair<std::pair<std::pair<uint64_t,
                                                                      uint64_t>,
                                                            uint64_t>,
                                                  uint64_t>,
                                        uint64_t>,
                              bool>,
                          uint64_t>,
                      uint64_t>,
                  uint64_t>,
              uint64_t>,
          uint64_t>,
      uint64_t>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(
                          std::make_pair(
                              std::make_pair(
                                  std::make_pair(
                                      std::make_pair(
                                          std::make_pair(
                                              std::make_pair(
                                                  test_page_base_alignment,
                                                  test_page_base_next_pc),
                                              test_page_boundary_cross),
                                          test_base_for_next_page_cross_1),
                                      test_base_for_next_page_cross_2),
                                  test_page_decomp_roundtrip),
                              test_page_offset_recompose),
                          test_page_recompose),
                      test_pc_inc2_wraparound),
                  test_pc_inc1_wrap),
              test_pc_inc2_wrap),
          test_disassemble_edge);
};

#endif // INCLUDED_PAGE_OPS
