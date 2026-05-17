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

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
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

  unsigned int length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return ((*a1).length() + 1);
    }
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(unsigned int n, const List<T1> &l, T1 default0);
};

struct LoadProgram {
  template <typename T1>
  static List<T1> update_nth(unsigned int n, T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth<T1>(n_, x, *a10));
      }
    }
  }

  struct state {
    List<unsigned int> rom;
    unsigned int prom_addr;
    unsigned int prom_data;
    bool prom_enable;

    // ACCESSORS
    state clone() const {
      return state{(*this).rom.clone(), (*this).prom_addr, (*this).prom_data,
                   (*this).prom_enable};
    }
  };

  struct state_extended {
    unsigned int regs_len;
    List<unsigned int> rom_ext;
    unsigned int pc;
    unsigned int stack_len;
    unsigned int prom_addr_ext;
    unsigned int prom_data_ext;
    bool prom_enable_ext;

    // ACCESSORS
    state_extended clone() const {
      return state_extended{(*this).regs_len,
                            (*this).rom_ext.clone(),
                            (*this).pc,
                            (*this).stack_len,
                            (*this).prom_addr_ext,
                            (*this).prom_data_ext,
                            (*this).prom_enable_ext};
    }
  };

  struct state_simple {
    List<unsigned int> rom_;
    unsigned int ptr_;

    // ACCESSORS
    state_simple clone() const {
      return state_simple{(*this).rom_.clone(), (*this).ptr_};
    }
  };

  static state set_prom_params(const state &s, unsigned int addr,
                               unsigned int data, bool enable);
  static state execute_wpm(const state &s);
  static state load_program(state s, unsigned int base,
                            const List<unsigned int> &bytes);
  static state_extended set_prom_params_ext(const state_extended &s,
                                            unsigned int addr,
                                            unsigned int data, bool enable);
  static state_extended execute_wpm_ext(const state_extended &s);
  static state_simple write_byte(const state_simple &s, unsigned int b);
  static state_simple load_program_simple(state_simple s,
                                          const List<unsigned int> &bytes);
  static inline const bool test_load_program_nil = []() {
    state sample =
        state{List<unsigned int>::cons(
                  10u, List<unsigned int>::cons(
                           11u, List<unsigned int>::cons(
                                    12u, List<unsigned int>::cons(
                                             13u, List<unsigned int>::nil())))),
              0u, 0u, false};
    state after =
        load_program(std::move(sample), 1u, List<unsigned int>::nil());
    return (ListDef::template nth<unsigned int>(0u, after.rom, 0u) == 10u &&
            (ListDef::template nth<unsigned int>(1u, after.rom, 0u) == 11u &&
             (ListDef::template nth<unsigned int>(2u, after.rom, 0u) == 12u &&
              ListDef::template nth<unsigned int>(3u, after.rom, 0u) == 13u)));
  }();
  static inline const bool test_load_program_cons_rom = []() {
    state sample =
        state{List<unsigned int>::cons(
                  10u, List<unsigned int>::cons(
                           11u, List<unsigned int>::cons(
                                    12u, List<unsigned int>::cons(
                                             13u, List<unsigned int>::nil())))),
              0u, 0u, false};
    state after = load_program(
        std::move(sample), 1u,
        List<unsigned int>::cons(
            99u, List<unsigned int>::cons(88u, List<unsigned int>::nil())));
    return (ListDef::template nth<unsigned int>(0u, after.rom, 0u) == 10u &&
            (ListDef::template nth<unsigned int>(1u, after.rom, 0u) == 99u &&
             (ListDef::template nth<unsigned int>(2u, after.rom, 0u) == 88u &&
              ListDef::template nth<unsigned int>(3u, after.rom, 0u) == 13u)));
  }();
  static inline const bool test_load_preserves_rom_length = []() {
    state sample =
        state{List<unsigned int>::cons(
                  10u, List<unsigned int>::cons(
                           11u, List<unsigned int>::cons(
                                    12u, List<unsigned int>::cons(
                                             13u, List<unsigned int>::nil())))),
              0u, 0u, false};
    state after =
        load_program(std::move(sample), 1u,
                     List<unsigned int>::cons(
                         99u, List<unsigned int>::cons(
                                  88u, List<unsigned int>::cons(
                                           77u, List<unsigned int>::nil()))));
    return std::move(after).rom.length() == 4u;
  }();
  static inline const bool test_load_program_step_preserves_wf_simple = []() {
    state_extended sample = state_extended{
        4u,
        List<unsigned int>::cons(
            10u, List<unsigned int>::cons(
                     11u, List<unsigned int>::cons(
                              12u, List<unsigned int>::cons(
                                       13u, List<unsigned int>::nil())))),
        100u,
        2u,
        0u,
        0u,
        false};
    state_extended after =
        execute_wpm_ext(set_prom_params_ext(std::move(sample), 1u, 99u, true));
    return (after.regs_len == 4u &&
            (after.rom_ext.length() == 4u &&
             (after.pc < 4096u && after.stack_len <= 3u)));
  }();
  static inline const bool test_load_program_step_rom_length_weak = []() {
    state sample =
        state{List<unsigned int>::cons(
                  10u, List<unsigned int>::cons(
                           11u, List<unsigned int>::cons(
                                    12u, List<unsigned int>::cons(
                                             13u, List<unsigned int>::nil())))),
              0u, 0u, false};
    state after =
        execute_wpm(set_prom_params(std::move(sample), 1u, 99u, true));
    return std::move(after).rom.length() == 4u;
  }();
  static inline const bool test_load_program_step_writes_at_base = []() {
    state sample =
        state{List<unsigned int>::cons(
                  10u, List<unsigned int>::cons(
                           11u, List<unsigned int>::cons(
                                    12u, List<unsigned int>::cons(
                                             13u, List<unsigned int>::nil())))),
              0u, 0u, false};
    state after =
        execute_wpm(set_prom_params(std::move(sample), 1u, 99u, true));
    return ListDef::template nth<unsigned int>(1u, std::move(after).rom, 0u) ==
           99u;
  }();
  static inline const unsigned int test_sequential_program_load = []() {
    state_simple sample = state_simple{
        List<unsigned int>::cons(
            0u, List<unsigned int>::cons(
                    0u, List<unsigned int>::cons(
                            0u, List<unsigned int>::cons(
                                    0u, List<unsigned int>::cons(
                                            0u, List<unsigned int>::nil()))))),
        1u};
    return ListDef::template nth<unsigned int>(
        2u,
        load_program_simple(
            std::move(sample),
            List<unsigned int>::cons(
                5u, List<unsigned int>::cons(
                        6u, List<unsigned int>::cons(
                                7u, List<unsigned int>::nil()))))
            .rom_,
        0u);
  }();
  static inline const std::pair<
      std::pair<
          std::pair<std::pair<std::pair<std::pair<bool, bool>, bool>, bool>,
                    bool>,
          bool>,
      unsigned int>
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
T1 ListDef::nth(unsigned int n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_LOAD_PROGRAM
