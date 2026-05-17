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
    A a0;
    std::unique_ptr<List<A>> a1;
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
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
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
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
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
  static unsigned int pow(unsigned int n, unsigned int m);
};

struct PageOps {
  struct state {
    unsigned int pc;

    // ACCESSORS
    state clone() const { return state{(*this).pc}; }
  };

  static unsigned int addr12_of_nat(unsigned int n);
  static unsigned int page_of(unsigned int p);
  static unsigned int page_base(unsigned int p);
  static unsigned int page_offset(unsigned int p);
  static unsigned int pc_inc1(const state &s);
  static unsigned int pc_inc2(const state &s);
  static unsigned int base_for_next1(const state &s);
  static unsigned int base_for_next2(const state &s);
  static unsigned int recompose(unsigned int p);
  static inline const unsigned int max_addr = ((
      (Nat::pow(2u, 12u) - 1u) > Nat::pow(2u, 12u) ? 0
                                                   : (Nat::pow(2u, 12u) - 1u)));

  struct instruction {
    // TYPES
    struct NOP {};

    struct LDM {
      unsigned int a0;
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

    static instruction ldm(unsigned int a0) { return instruction(LDM{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, unsigned int &>
  static T1 instruction_rect(T1 f, F1 &&f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename instruction::LDM>(i.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, unsigned int &>
  static T1 instruction_rec(T1 f, F1 &&f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename instruction::LDM>(i.v());
      return f0(a0);
    }
  }

  static instruction decode(unsigned int b1, unsigned int b2);

  template <typename T1> static List<T1> drop(unsigned int n, List<T1> l) {
    if (n <= 0) {
      return l;
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v_mut())) {
        return List<T1>::nil();
      } else {
        auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v_mut());
        return drop<T1>(n_, *a1);
      }
    }
  }

  static std::optional<std::pair<instruction, unsigned int>>
  disassemble(const List<unsigned int> &rom, unsigned int addr);
  static inline const unsigned int test_page_base_alignment =
      (256u ? page_base(777u) % 256u : page_base(777u));
  static inline const unsigned int test_page_base_next_pc = []() {
    state s = state{511u};
    return (base_for_next1(s) + base_for_next2(s));
  }();
  static inline const unsigned int test_page_boundary_cross =
      base_for_next1(state{255u});
  static inline const unsigned int test_base_for_next_page_cross_1 =
      base_for_next1(state{255u});
  static inline const unsigned int test_base_for_next_page_cross_2 =
      base_for_next2(state{255u});
  static inline const bool test_page_decomp_roundtrip =
      (((256u ? 1027u / 256u : 0) * 256u) + (256u ? 1027u % 256u : 1027u)) ==
      1027u;
  static inline const unsigned int test_page_offset_recompose =
      recompose(addr12_of_nat(1027u));
  static inline const unsigned int test_page_recompose =
      recompose(addr12_of_nat(1027u));
  static inline const unsigned int test_pc_inc2_wraparound =
      pc_inc2(state{max_addr});
  static inline const unsigned int test_pc_inc1_wrap = pc_inc1(state{max_addr});
  static inline const unsigned int test_pc_inc2_wrap = pc_inc2(state{max_addr});
  static inline const unsigned int test_disassemble_edge =
      []() -> unsigned int {
    auto _cs = disassemble(
        List<unsigned int>::cons(
            0u, List<unsigned int>::cons(
                    7u, List<unsigned int>::cons(
                            9u, List<unsigned int>::cons(
                                    11u, List<unsigned int>::nil())))),
        0u);
    if (_cs.has_value()) {
      const std::pair<instruction, unsigned int> &p = *_cs;
      const instruction &_x = p.first;
      const unsigned int &next = p.second;
      return next;
    } else {
      return 0u;
    }
  }();
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<
                          std::pair<
                              std::pair<
                                  std::pair<std::pair<std::pair<unsigned int,
                                                                unsigned int>,
                                                      unsigned int>,
                                            unsigned int>,
                                  unsigned int>,
                              bool>,
                          unsigned int>,
                      unsigned int>,
                  unsigned int>,
              unsigned int>,
          unsigned int>,
      unsigned int>
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
