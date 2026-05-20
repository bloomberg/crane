#ifndef INCLUDED_JUMP_TARGETS
#define INCLUDED_JUMP_TARGETS

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
    std::unique_ptr<List<A>> l;
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
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
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
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

struct JumpTargets {
  struct instr_collection {
    // TYPES
    struct JUN_coll {
      uint64_t a0;
    };

    struct JMS_coll {
      uint64_t a0;
    };

    struct NOP_coll {};

    using variant_t = std::variant<JUN_coll, JMS_coll, NOP_coll>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instr_collection() {}

    explicit instr_collection(JUN_coll _v) : v_(std::move(_v)) {}

    explicit instr_collection(JMS_coll _v) : v_(std::move(_v)) {}

    explicit instr_collection(NOP_coll _v) : v_(_v) {}

    instr_collection(const instr_collection &_other)
        : v_(std::move(_other.clone().v_)) {}

    instr_collection(instr_collection &&_other) noexcept
        : v_(std::move(_other.v_)) {}

    instr_collection &operator=(const instr_collection &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    instr_collection &operator=(instr_collection &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    instr_collection clone() const {
      if (std::holds_alternative<JUN_coll>(this->v())) {
        const auto &[a0] = std::get<JUN_coll>(this->v());
        return instr_collection(JUN_coll{a0});
      } else if (std::holds_alternative<JMS_coll>(this->v())) {
        const auto &[a0] = std::get<JMS_coll>(this->v());
        return instr_collection(JMS_coll{a0});
      } else {
        return instr_collection(NOP_coll{});
      }
    }

    // CREATORS
    static instr_collection jun_coll(uint64_t a0) {
      return instr_collection(JUN_coll{a0});
    }

    static instr_collection jms_coll(uint64_t a0) {
      return instr_collection(JMS_coll{a0});
    }

    static instr_collection nop_coll() { return instr_collection(NOP_coll{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    std::optional<uint64_t> jump_target_collection() const {
      if (std::holds_alternative<typename instr_collection::JUN_coll>(
              this->v())) {
        const auto &[a0] =
            std::get<typename instr_collection::JUN_coll>(this->v());
        return std::make_optional<uint64_t>(a0);
      } else if (std::holds_alternative<typename instr_collection::JMS_coll>(
                     this->v())) {
        const auto &[a0] =
            std::get<typename instr_collection::JMS_coll>(this->v());
        return std::make_optional<uint64_t>(a0);
      } else {
        return std::optional<uint64_t>();
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 instr_collection_rec(F0 &&f, F1 &&f0, T1 f1) const {
      if (std::holds_alternative<typename instr_collection::JUN_coll>(
              this->v())) {
        const auto &[a0] =
            std::get<typename instr_collection::JUN_coll>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename instr_collection::JMS_coll>(
                     this->v())) {
        const auto &[a0] =
            std::get<typename instr_collection::JMS_coll>(this->v());
        return f0(a0);
      } else {
        return f1;
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 instr_collection_rect(F0 &&f, F1 &&f0, T1 f1) const {
      if (std::holds_alternative<typename instr_collection::JUN_coll>(
              this->v())) {
        const auto &[a0] =
            std::get<typename instr_collection::JUN_coll>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename instr_collection::JMS_coll>(
                     this->v())) {
        const auto &[a0] =
            std::get<typename instr_collection::JMS_coll>(this->v());
        return f0(a0);
      } else {
        return f1;
      }
    }
  };

  static List<uint64_t> collect_targets(const List<instr_collection> &prog);
  static inline const uint64_t test_collection =
      collect_targets(List<instr_collection>::cons(
                          instr_collection::jun_coll(UINT64_C(17)),
                          List<instr_collection>::cons(
                              instr_collection::nop_coll(),
                              List<instr_collection>::cons(
                                  instr_collection::jms_coll(UINT64_C(511)),
                                  List<instr_collection>::cons(
                                      instr_collection::nop_coll(),
                                      List<instr_collection>::nil())))))
          .length();

  struct instr_region {
    // TYPES
    struct JUN_reg {
      uint64_t a0;
    };

    struct JMS_reg {
      uint64_t a0;
    };

    struct NOP_reg {};

    using variant_t = std::variant<JUN_reg, JMS_reg, NOP_reg>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instr_region() {}

    explicit instr_region(JUN_reg _v) : v_(std::move(_v)) {}

    explicit instr_region(JMS_reg _v) : v_(std::move(_v)) {}

    explicit instr_region(NOP_reg _v) : v_(_v) {}

    instr_region(const instr_region &_other)
        : v_(std::move(_other.clone().v_)) {}

    instr_region(instr_region &&_other) noexcept : v_(std::move(_other.v_)) {}

    instr_region &operator=(const instr_region &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    instr_region &operator=(instr_region &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    instr_region clone() const {
      if (std::holds_alternative<JUN_reg>(this->v())) {
        const auto &[a0] = std::get<JUN_reg>(this->v());
        return instr_region(JUN_reg{a0});
      } else if (std::holds_alternative<JMS_reg>(this->v())) {
        const auto &[a0] = std::get<JMS_reg>(this->v());
        return instr_region(JMS_reg{a0});
      } else {
        return instr_region(NOP_reg{});
      }
    }

    // CREATORS
    static instr_region jun_reg(uint64_t a0) {
      return instr_region(JUN_reg{a0});
    }

    static instr_region jms_reg(uint64_t a0) {
      return instr_region(JMS_reg{a0});
    }

    static instr_region nop_reg() { return instr_region(NOP_reg{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    std::optional<uint64_t> jump_target_region() const {
      if (std::holds_alternative<typename instr_region::JUN_reg>(this->v())) {
        const auto &[a0] = std::get<typename instr_region::JUN_reg>(this->v());
        return std::make_optional<uint64_t>(a0);
      } else if (std::holds_alternative<typename instr_region::JMS_reg>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_region::JMS_reg>(this->v());
        return std::make_optional<uint64_t>(a0);
      } else {
        return std::optional<uint64_t>();
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 instr_region_rec(F0 &&f, F1 &&f0, T1 f1) const {
      if (std::holds_alternative<typename instr_region::JUN_reg>(this->v())) {
        const auto &[a0] = std::get<typename instr_region::JUN_reg>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename instr_region::JMS_reg>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_region::JMS_reg>(this->v());
        return f0(a0);
      } else {
        return f1;
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 instr_region_rect(F0 &&f, F1 &&f0, T1 f1) const {
      if (std::holds_alternative<typename instr_region::JUN_reg>(this->v())) {
        const auto &[a0] = std::get<typename instr_region::JUN_reg>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename instr_region::JMS_reg>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_region::JMS_reg>(this->v());
        return f0(a0);
      } else {
        return f1;
      }
    }
  };

  struct layout {
    uint64_t base_;
    uint64_t code_;

    // ACCESSORS
    layout clone() const { return layout{this->base_, this->code_}; }
  };

  static bool addr_in_region(uint64_t addr, const layout &l);
  static bool in_layout(const layout &l, const instr_region &i);
  static inline const bool test_region_check = in_layout(
      layout{UINT64_C(16), UINT64_C(32)}, instr_region::jun_reg(UINT64_C(40)));

  struct instr_jms {
    // TYPES
    struct JUN_jms {
      uint64_t a0;
    };

    struct JMS_jms {
      uint64_t a0;
    };

    struct NOP_jms {};

    using variant_t = std::variant<JUN_jms, JMS_jms, NOP_jms>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instr_jms() {}

    explicit instr_jms(JUN_jms _v) : v_(std::move(_v)) {}

    explicit instr_jms(JMS_jms _v) : v_(std::move(_v)) {}

    explicit instr_jms(NOP_jms _v) : v_(_v) {}

    instr_jms(const instr_jms &_other) : v_(std::move(_other.clone().v_)) {}

    instr_jms(instr_jms &&_other) noexcept : v_(std::move(_other.v_)) {}

    instr_jms &operator=(const instr_jms &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    instr_jms &operator=(instr_jms &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    instr_jms clone() const {
      if (std::holds_alternative<JUN_jms>(this->v())) {
        const auto &[a0] = std::get<JUN_jms>(this->v());
        return instr_jms(JUN_jms{a0});
      } else if (std::holds_alternative<JMS_jms>(this->v())) {
        const auto &[a0] = std::get<JMS_jms>(this->v());
        return instr_jms(JMS_jms{a0});
      } else {
        return instr_jms(NOP_jms{});
      }
    }

    // CREATORS
    static instr_jms jun_jms(uint64_t a0) { return instr_jms(JUN_jms{a0}); }

    static instr_jms jms_jms(uint64_t a0) { return instr_jms(JMS_jms{a0}); }

    static instr_jms nop_jms() { return instr_jms(NOP_jms{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    std::optional<uint64_t> jump_target_jms() const {
      if (std::holds_alternative<typename instr_jms::JUN_jms>(this->v())) {
        const auto &[a0] = std::get<typename instr_jms::JUN_jms>(this->v());
        return std::make_optional<uint64_t>(a0);
      } else if (std::holds_alternative<typename instr_jms::JMS_jms>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_jms::JMS_jms>(this->v());
        return std::make_optional<uint64_t>(a0);
      } else {
        return std::optional<uint64_t>();
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 instr_jms_rec(F0 &&f, F1 &&f0, T1 f1) const {
      if (std::holds_alternative<typename instr_jms::JUN_jms>(this->v())) {
        const auto &[a0] = std::get<typename instr_jms::JUN_jms>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename instr_jms::JMS_jms>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_jms::JMS_jms>(this->v());
        return f0(a0);
      } else {
        return f1;
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 instr_jms_rect(F0 &&f, F1 &&f0, T1 f1) const {
      if (std::holds_alternative<typename instr_jms::JUN_jms>(this->v())) {
        const auto &[a0] = std::get<typename instr_jms::JUN_jms>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename instr_jms::JMS_jms>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_jms::JMS_jms>(this->v());
        return f0(a0);
      } else {
        return f1;
      }
    }
  };

  static uint64_t option_nat_or_zero(const std::optional<uint64_t> &o);
  static inline const uint64_t test_jms =
      option_nat_or_zero(instr_jms::jms_jms(UINT64_C(144)).jump_target_jms());

  struct instr_jun {
    // TYPES
    struct JUN_jun {
      uint64_t a0;
    };

    struct JMS_jun {
      uint64_t a0;
    };

    struct NOP_jun {};

    using variant_t = std::variant<JUN_jun, JMS_jun, NOP_jun>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instr_jun() {}

    explicit instr_jun(JUN_jun _v) : v_(std::move(_v)) {}

    explicit instr_jun(JMS_jun _v) : v_(std::move(_v)) {}

    explicit instr_jun(NOP_jun _v) : v_(_v) {}

    instr_jun(const instr_jun &_other) : v_(std::move(_other.clone().v_)) {}

    instr_jun(instr_jun &&_other) noexcept : v_(std::move(_other.v_)) {}

    instr_jun &operator=(const instr_jun &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    instr_jun &operator=(instr_jun &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    instr_jun clone() const {
      if (std::holds_alternative<JUN_jun>(this->v())) {
        const auto &[a0] = std::get<JUN_jun>(this->v());
        return instr_jun(JUN_jun{a0});
      } else if (std::holds_alternative<JMS_jun>(this->v())) {
        const auto &[a0] = std::get<JMS_jun>(this->v());
        return instr_jun(JMS_jun{a0});
      } else {
        return instr_jun(NOP_jun{});
      }
    }

    // CREATORS
    static instr_jun jun_jun(uint64_t a0) { return instr_jun(JUN_jun{a0}); }

    static instr_jun jms_jun(uint64_t a0) { return instr_jun(JMS_jun{a0}); }

    static instr_jun nop_jun() { return instr_jun(NOP_jun{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    std::optional<uint64_t> jump_target_jun() const {
      if (std::holds_alternative<typename instr_jun::JUN_jun>(this->v())) {
        const auto &[a0] = std::get<typename instr_jun::JUN_jun>(this->v());
        return std::make_optional<uint64_t>(a0);
      } else if (std::holds_alternative<typename instr_jun::JMS_jun>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_jun::JMS_jun>(this->v());
        return std::make_optional<uint64_t>(a0);
      } else {
        return std::optional<uint64_t>();
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 instr_jun_rec(F0 &&f, F1 &&f0, T1 f1) const {
      if (std::holds_alternative<typename instr_jun::JUN_jun>(this->v())) {
        const auto &[a0] = std::get<typename instr_jun::JUN_jun>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename instr_jun::JMS_jun>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_jun::JMS_jun>(this->v());
        return f0(a0);
      } else {
        return f1;
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 instr_jun_rect(F0 &&f, F1 &&f0, T1 f1) const {
      if (std::holds_alternative<typename instr_jun::JUN_jun>(this->v())) {
        const auto &[a0] = std::get<typename instr_jun::JUN_jun>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename instr_jun::JMS_jun>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_jun::JMS_jun>(this->v());
        return f0(a0);
      } else {
        return f1;
      }
    }
  };

  static uint64_t target_default(const std::optional<uint64_t> &o);
  static inline const uint64_t test_jun =
      target_default(instr_jun::jun_jun(UINT64_C(511)).jump_target_jun());

  static inline const std::pair<std::pair<std::pair<uint64_t, bool>, uint64_t>,
                                uint64_t>
      t = std::make_pair(
          std::make_pair(std::make_pair(test_collection, test_region_check),
                         test_jms),
          test_jun);
};

#endif // INCLUDED_JUMP_TARGETS
