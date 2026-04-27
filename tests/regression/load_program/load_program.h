#ifndef INCLUDED_LOAD_PROGRAM
#define INCLUDED_LOAD_PROGRAM

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      t_A __c0;
      if constexpr (
          requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
          requires { d_a0->clone(); } && requires { d_a0.get(); }) {
        using _E = std::remove_cvref_t<decltype(*d_a0)>;
        __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
      } else if constexpr (requires { d_a0.clone(); }) {
        __c0 = d_a0.clone();
      } else {
        __c0 = d_a0;
      }
      return List<t_A>(
          Cons{std::move(__c0),
               d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{
          [&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
            if constexpr (
                requires { *__v; } &&
                !requires { std::declval<_DstT>().get(); })
              return _DstT(*__v);
            else if constexpr (
                !requires { *__v; } &&
                requires { std::declval<_DstT>().get(); }) {
              using _E =
                  std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
              return std::make_unique<_E>(std::move(__v));
            } else
              return _DstT(__v);
          }(d_a0),
          d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int &n, const List<T1> &l, const T1 default0);
};

struct LoadProgram {
  template <typename T1>
  __attribute__((pure)) static List<T1>
  update_nth(const unsigned int &n, const T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *(d_a1));
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(d_a00, update_nth<T1>(n_, x, *(d_a10)));
      }
    }
  }

  struct state {
    List<unsigned int> rom;
    unsigned int prom_addr;
    unsigned int prom_data;
    bool prom_enable;

    __attribute__((pure)) state *operator->() { return this; }

    __attribute__((pure)) const state *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state clone() const {
      return state{
          (*(this)).rom.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_addr),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_data),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_enable)};
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

    __attribute__((pure)) state_extended *operator->() { return this; }

    __attribute__((pure)) const state_extended *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) state_extended clone() const {
      return state_extended{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).regs_len),
          (*(this)).rom_ext.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).pc),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).stack_len),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_addr_ext),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_data_ext),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_enable_ext)};
    }
  };

  struct state_simple {
    List<unsigned int> rom_;
    unsigned int ptr_;

    __attribute__((pure)) state_simple *operator->() { return this; }

    __attribute__((pure)) const state_simple *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) state_simple clone() const {
      return state_simple{
          (*(this)).rom_.clone(), [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).ptr_)};
    }
  };

  __attribute__((pure)) static state set_prom_params(const state &s,
                                                     unsigned int addr,
                                                     unsigned int data,
                                                     bool enable);
  __attribute__((pure)) static state execute_wpm(const state &s);
  __attribute__((pure)) static state
  load_program(state s, const unsigned int &base,
               const List<unsigned int> &bytes);
  __attribute__((pure)) static state_extended
  set_prom_params_ext(const state_extended &s, unsigned int addr,
                      unsigned int data, bool enable);
  __attribute__((pure)) static state_extended
  execute_wpm_ext(const state_extended &s);
  __attribute__((pure)) static state_simple write_byte(const state_simple &s,
                                                       const unsigned int &b);
  __attribute__((pure)) static state_simple
  load_program_simple(state_simple s, const List<unsigned int> &bytes);
  static inline const bool test_load_program_nil = []() {
    state sample =
        state{List<unsigned int>::cons(
                  10u, List<unsigned int>::cons(
                           11u, List<unsigned int>::cons(
                                    12u, List<unsigned int>::cons(
                                             13u, List<unsigned int>::nil())))),
              0u, 0u, false};
    state after = load_program(sample, 1u, List<unsigned int>::nil());
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
        sample, 1u,
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
        load_program(sample, 1u,
                     List<unsigned int>::cons(
                         99u, List<unsigned int>::cons(
                                  88u, List<unsigned int>::cons(
                                           77u, List<unsigned int>::nil()))));
    return after.rom.length() == 4u;
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
        execute_wpm_ext(set_prom_params_ext(sample, 1u, 99u, true));
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
    state after = execute_wpm(set_prom_params(sample, 1u, 99u, true));
    return after.rom.length() == 4u;
  }();
  static inline const bool test_load_program_step_writes_at_base = []() {
    state sample =
        state{List<unsigned int>::cons(
                  10u, List<unsigned int>::cons(
                           11u, List<unsigned int>::cons(
                                    12u, List<unsigned int>::cons(
                                             13u, List<unsigned int>::nil())))),
              0u, 0u, false};
    state after = execute_wpm(set_prom_params(sample, 1u, 99u, true));
    return ListDef::template nth<unsigned int>(1u, after.rom, 0u) == 99u;
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
            sample, List<unsigned int>::cons(
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
T1 ListDef::nth(const unsigned int &n, const List<T1> &l, const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *(d_a10), default0);
    }
  }
}

#endif // INCLUDED_LOAD_PROGRAM
