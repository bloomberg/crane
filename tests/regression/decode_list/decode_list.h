#ifndef INCLUDED_DECODE_LIST
#define INCLUDED_DECODE_LIST

#include <memory>
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

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct DecodeList {
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
  static List<instruction> decode_list(const List<uint64_t> &bytes);
  static inline const uint64_t t_empty =
      decode_list(List<uint64_t>::nil()).length();
  static inline const uint64_t t_odd_tail = []() {
    auto &&_sv0 = decode_list(List<uint64_t>::cons(
        UINT64_C(0),
        List<uint64_t>::cons(
            UINT64_C(99),
            List<uint64_t>::cons(UINT64_C(42), List<uint64_t>::nil()))));
    if (std::holds_alternative<typename List<instruction>::Nil>(_sv0.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a00, a10] =
          std::get<typename List<instruction>::Cons>(_sv0.v());
      if (std::holds_alternative<typename instruction::NOP>(a00.v())) {
        auto &&_sv = *a10;
        if (std::holds_alternative<typename List<instruction>::Nil>(_sv.v())) {
          return UINT64_C(1);
        } else {
          return UINT64_C(0);
        }
      } else {
        return UINT64_C(0);
      }
    }
  }();
  static inline const uint64_t t_pair_count =
      decode_list(
          List<uint64_t>::cons(
              UINT64_C(0),
              List<uint64_t>::cons(
                  UINT64_C(1),
                  List<uint64_t>::cons(
                      UINT64_C(2), List<uint64_t>::cons(
                                       UINT64_C(3), List<uint64_t>::nil())))))
          .length();
  static inline const uint64_t t_single_pair =
      decode_list(List<uint64_t>::cons(
                      UINT64_C(0),
                      List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil())))
          .length();
};

#endif // INCLUDED_DECODE_LIST
