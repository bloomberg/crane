#ifndef INCLUDED_LOAD_PROGRAM
#define INCLUDED_LOAD_PROGRAM

#include <memory>
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

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct LoadProgram {
  template <typename T1>
  static List<T1> update_nth(uint64_t n, T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth<T1>(n_, x, *a10));
      }
    }
  }

  struct state {
    List<uint64_t> rom;
    uint64_t prom_addr;
    uint64_t prom_data;
    bool prom_enable;

    // ACCESSORS
    state clone() const {
      return state{this->rom.clone(), this->prom_addr, this->prom_data,
                   this->prom_enable};
    }
  };

  struct state_extended {
    uint64_t regs_len;
    List<uint64_t> rom_ext;
    uint64_t pc;
    uint64_t stack_len;
    uint64_t prom_addr_ext;
    uint64_t prom_data_ext;
    bool prom_enable_ext;

    // ACCESSORS
    state_extended clone() const {
      return state_extended{
          this->regs_len,       this->rom_ext.clone(), this->pc,
          this->stack_len,      this->prom_addr_ext,   this->prom_data_ext,
          this->prom_enable_ext};
    }
  };

  struct state_simple {
    List<uint64_t> rom_;
    uint64_t ptr_;

    // ACCESSORS
    state_simple clone() const {
      return state_simple{this->rom_.clone(), this->ptr_};
    }
  };

  static state set_prom_params(const state &s, uint64_t addr, uint64_t data,
                               bool enable);
  static state execute_wpm(const state &s);
  static state load_program(state s, uint64_t base,
                            const List<uint64_t> &bytes);
  static state_extended set_prom_params_ext(const state_extended &s,
                                            uint64_t addr, uint64_t data,
                                            bool enable);
  static state_extended execute_wpm_ext(const state_extended &s);
  static state_simple write_byte(const state_simple &s, uint64_t b);
  static state_simple load_program_simple(state_simple s,
                                          const List<uint64_t> &bytes);
  static inline const bool test_load_program_nil = []() {
    state sample = state{
        List<uint64_t>::cons(
            UINT64_C(10),
            List<uint64_t>::cons(
                UINT64_C(11),
                List<uint64_t>::cons(
                    UINT64_C(12), List<uint64_t>::cons(
                                      UINT64_C(13), List<uint64_t>::nil())))),
        UINT64_C(0), UINT64_C(0), false};
    state after =
        load_program(std::move(sample), UINT64_C(1), List<uint64_t>::nil());
    return (ListDef::template nth<uint64_t>(UINT64_C(0), after.rom,
                                            UINT64_C(0)) == UINT64_C(10) &&
            (ListDef::template nth<uint64_t>(UINT64_C(1), after.rom,
                                             UINT64_C(0)) == UINT64_C(11) &&
             (ListDef::template nth<uint64_t>(UINT64_C(2), after.rom,
                                              UINT64_C(0)) == UINT64_C(12) &&
              ListDef::template nth<uint64_t>(UINT64_C(3), after.rom,
                                              UINT64_C(0)) == UINT64_C(13))));
  }();
  static inline const bool test_load_program_cons_rom = []() {
    state sample = state{
        List<uint64_t>::cons(
            UINT64_C(10),
            List<uint64_t>::cons(
                UINT64_C(11),
                List<uint64_t>::cons(
                    UINT64_C(12), List<uint64_t>::cons(
                                      UINT64_C(13), List<uint64_t>::nil())))),
        UINT64_C(0), UINT64_C(0), false};
    state after = load_program(
        std::move(sample), UINT64_C(1),
        List<uint64_t>::cons(
            UINT64_C(99),
            List<uint64_t>::cons(UINT64_C(88), List<uint64_t>::nil())));
    return (ListDef::template nth<uint64_t>(UINT64_C(0), after.rom,
                                            UINT64_C(0)) == UINT64_C(10) &&
            (ListDef::template nth<uint64_t>(UINT64_C(1), after.rom,
                                             UINT64_C(0)) == UINT64_C(99) &&
             (ListDef::template nth<uint64_t>(UINT64_C(2), after.rom,
                                              UINT64_C(0)) == UINT64_C(88) &&
              ListDef::template nth<uint64_t>(UINT64_C(3), after.rom,
                                              UINT64_C(0)) == UINT64_C(13))));
  }();
  static inline const bool test_load_preserves_rom_length = []() {
    state sample = state{
        List<uint64_t>::cons(
            UINT64_C(10),
            List<uint64_t>::cons(
                UINT64_C(11),
                List<uint64_t>::cons(
                    UINT64_C(12), List<uint64_t>::cons(
                                      UINT64_C(13), List<uint64_t>::nil())))),
        UINT64_C(0), UINT64_C(0), false};
    state after = load_program(
        std::move(sample), UINT64_C(1),
        List<uint64_t>::cons(
            UINT64_C(99),
            List<uint64_t>::cons(
                UINT64_C(88),
                List<uint64_t>::cons(UINT64_C(77), List<uint64_t>::nil()))));
    return std::move(after).rom.length() == UINT64_C(4);
  }();
  static inline const bool test_load_program_step_preserves_wf_simple = []() {
    state_extended sample = state_extended{
        UINT64_C(4),
        List<uint64_t>::cons(
            UINT64_C(10),
            List<uint64_t>::cons(
                UINT64_C(11),
                List<uint64_t>::cons(
                    UINT64_C(12), List<uint64_t>::cons(
                                      UINT64_C(13), List<uint64_t>::nil())))),
        UINT64_C(100),
        UINT64_C(2),
        UINT64_C(0),
        UINT64_C(0),
        false};
    state_extended after = execute_wpm_ext(set_prom_params_ext(
        std::move(sample), UINT64_C(1), UINT64_C(99), true));
    return (after.regs_len == UINT64_C(4) &&
            (after.rom_ext.length() == UINT64_C(4) &&
             (after.pc < UINT64_C(4096) && after.stack_len <= UINT64_C(3))));
  }();
  static inline const bool test_load_program_step_rom_length_weak = []() {
    state sample = state{
        List<uint64_t>::cons(
            UINT64_C(10),
            List<uint64_t>::cons(
                UINT64_C(11),
                List<uint64_t>::cons(
                    UINT64_C(12), List<uint64_t>::cons(
                                      UINT64_C(13), List<uint64_t>::nil())))),
        UINT64_C(0), UINT64_C(0), false};
    state after = execute_wpm(
        set_prom_params(std::move(sample), UINT64_C(1), UINT64_C(99), true));
    return std::move(after).rom.length() == UINT64_C(4);
  }();
  static inline const bool test_load_program_step_writes_at_base = []() {
    state sample = state{
        List<uint64_t>::cons(
            UINT64_C(10),
            List<uint64_t>::cons(
                UINT64_C(11),
                List<uint64_t>::cons(
                    UINT64_C(12), List<uint64_t>::cons(
                                      UINT64_C(13), List<uint64_t>::nil())))),
        UINT64_C(0), UINT64_C(0), false};
    state after = execute_wpm(
        set_prom_params(std::move(sample), UINT64_C(1), UINT64_C(99), true));
    return ListDef::template nth<uint64_t>(UINT64_C(1), std::move(after).rom,
                                           UINT64_C(0)) == UINT64_C(99);
  }();
  static inline const uint64_t test_sequential_program_load = []() {
    state_simple sample = state_simple{
        List<uint64_t>::cons(
            UINT64_C(0),
            List<uint64_t>::cons(
                UINT64_C(0),
                List<uint64_t>::cons(
                    UINT64_C(0),
                    List<uint64_t>::cons(
                        UINT64_C(0),
                        List<uint64_t>::cons(UINT64_C(0),
                                             List<uint64_t>::nil()))))),
        UINT64_C(1)};
    return ListDef::template nth<uint64_t>(
        UINT64_C(2),
        load_program_simple(
            std::move(sample),
            List<uint64_t>::cons(
                UINT64_C(5),
                List<uint64_t>::cons(
                    UINT64_C(6),
                    List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil()))))
            .rom_,
        UINT64_C(0));
  }();
  static inline const std::pair<
      std::pair<
          std::pair<std::pair<std::pair<std::pair<bool, bool>, bool>, bool>,
                    bool>,
          bool>,
      uint64_t>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(std::make_pair(test_load_program_nil,
                                                    test_load_program_cons_rom),
                                     test_load_preserves_rom_length),
                      test_load_program_step_preserves_wf_simple),
                  test_load_program_step_rom_length_weak),
              test_load_program_step_writes_at_base),
          test_sequential_program_load);
};

template <typename T1>
T1 ListDef::nth(uint64_t n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_LOAD_PROGRAM
