#ifndef INCLUDED_JUMP_TARGETS
#define INCLUDED_JUMP_TARGETS

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
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
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
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

struct JumpTargets {
  struct instr_collection {
    // TYPES
    struct JUN_coll {
      unsigned int d_a0;
    };

    struct JMS_coll {
      unsigned int d_a0;
    };

    struct NOP_coll {};

    using variant_t = std::variant<JUN_coll, JMS_coll, NOP_coll>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    instr_collection() {}

    explicit instr_collection(JUN_coll _v) : d_v_(std::move(_v)) {}

    explicit instr_collection(JMS_coll _v) : d_v_(std::move(_v)) {}

    explicit instr_collection(NOP_coll _v) : d_v_(_v) {}

    instr_collection(const instr_collection &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instr_collection(instr_collection &&_other)
        : d_v_(std::move(_other.d_v_)) {}

    instr_collection &operator=(const instr_collection &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    instr_collection &operator=(instr_collection &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instr_collection clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<JUN_coll>(_sv.v())) {
        const auto &[d_a0] = std::get<JUN_coll>(_sv.v());
        return instr_collection(JUN_coll{d_a0});
      } else if (std::holds_alternative<JMS_coll>(_sv.v())) {
        const auto &[d_a0] = std::get<JMS_coll>(_sv.v());
        return instr_collection(JMS_coll{d_a0});
      } else {
        return instr_collection(NOP_coll{});
      }
    }

    // CREATORS
    __attribute__((pure)) static instr_collection jun_coll(unsigned int a0) {
      return instr_collection(JUN_coll{std::move(a0)});
    }

    __attribute__((pure)) static instr_collection jms_coll(unsigned int a0) {
      return instr_collection(JMS_coll{std::move(a0)});
    }

    __attribute__((pure)) static instr_collection nop_coll() {
      return instr_collection(NOP_coll{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) instr_collection *operator->() { return this; }

    __attribute__((pure)) const instr_collection *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = instr_collection(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) std::optional<unsigned int>
    jump_target_collection() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_collection::JUN_coll>(
              _sv.v())) {
        const auto &[d_a0] =
            std::get<typename instr_collection::JUN_coll>(_sv.v());
        return std::make_optional<unsigned int>(d_a0);
      } else if (std::holds_alternative<typename instr_collection::JMS_coll>(
                     _sv.v())) {
        const auto &[d_a0] =
            std::get<typename instr_collection::JMS_coll>(_sv.v());
        return std::make_optional<unsigned int>(d_a0);
      } else {
        return std::optional<unsigned int>();
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 instr_collection_rec(F0 &&f, F1 &&f0, const T1 f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_collection::JUN_coll>(
              _sv.v())) {
        const auto &[d_a0] =
            std::get<typename instr_collection::JUN_coll>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename instr_collection::JMS_coll>(
                     _sv.v())) {
        const auto &[d_a0] =
            std::get<typename instr_collection::JMS_coll>(_sv.v());
        return f0(d_a0);
      } else {
        return f1;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 instr_collection_rect(F0 &&f, F1 &&f0, const T1 f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_collection::JUN_coll>(
              _sv.v())) {
        const auto &[d_a0] =
            std::get<typename instr_collection::JUN_coll>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename instr_collection::JMS_coll>(
                     _sv.v())) {
        const auto &[d_a0] =
            std::get<typename instr_collection::JMS_coll>(_sv.v());
        return f0(d_a0);
      } else {
        return f1;
      }
    }
  };

  __attribute__((pure)) static List<unsigned int>
  collect_targets(const List<instr_collection> &prog);
  static inline const unsigned int test_collection =
      collect_targets(List<instr_collection>::cons(
                          instr_collection::jun_coll(17u),
                          List<instr_collection>::cons(
                              instr_collection::nop_coll(),
                              List<instr_collection>::cons(
                                  instr_collection::jms_coll(511u),
                                  List<instr_collection>::cons(
                                      instr_collection::nop_coll(),
                                      List<instr_collection>::nil())))))
          .length();

  struct instr_region {
    // TYPES
    struct JUN_reg {
      unsigned int d_a0;
    };

    struct JMS_reg {
      unsigned int d_a0;
    };

    struct NOP_reg {};

    using variant_t = std::variant<JUN_reg, JMS_reg, NOP_reg>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    instr_region() {}

    explicit instr_region(JUN_reg _v) : d_v_(std::move(_v)) {}

    explicit instr_region(JMS_reg _v) : d_v_(std::move(_v)) {}

    explicit instr_region(NOP_reg _v) : d_v_(_v) {}

    instr_region(const instr_region &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instr_region(instr_region &&_other) : d_v_(std::move(_other.d_v_)) {}

    instr_region &operator=(const instr_region &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    instr_region &operator=(instr_region &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instr_region clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<JUN_reg>(_sv.v())) {
        const auto &[d_a0] = std::get<JUN_reg>(_sv.v());
        return instr_region(JUN_reg{d_a0});
      } else if (std::holds_alternative<JMS_reg>(_sv.v())) {
        const auto &[d_a0] = std::get<JMS_reg>(_sv.v());
        return instr_region(JMS_reg{d_a0});
      } else {
        return instr_region(NOP_reg{});
      }
    }

    // CREATORS
    __attribute__((pure)) static instr_region jun_reg(unsigned int a0) {
      return instr_region(JUN_reg{std::move(a0)});
    }

    __attribute__((pure)) static instr_region jms_reg(unsigned int a0) {
      return instr_region(JMS_reg{std::move(a0)});
    }

    __attribute__((pure)) static instr_region nop_reg() {
      return instr_region(NOP_reg{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) instr_region *operator->() { return this; }

    __attribute__((pure)) const instr_region *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = instr_region(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) std::optional<unsigned int>
    jump_target_region() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_region::JUN_reg>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_region::JUN_reg>(_sv.v());
        return std::make_optional<unsigned int>(d_a0);
      } else if (std::holds_alternative<typename instr_region::JMS_reg>(
                     _sv.v())) {
        const auto &[d_a0] = std::get<typename instr_region::JMS_reg>(_sv.v());
        return std::make_optional<unsigned int>(d_a0);
      } else {
        return std::optional<unsigned int>();
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 instr_region_rec(F0 &&f, F1 &&f0, const T1 f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_region::JUN_reg>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_region::JUN_reg>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename instr_region::JMS_reg>(
                     _sv.v())) {
        const auto &[d_a0] = std::get<typename instr_region::JMS_reg>(_sv.v());
        return f0(d_a0);
      } else {
        return f1;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 instr_region_rect(F0 &&f, F1 &&f0, const T1 f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_region::JUN_reg>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_region::JUN_reg>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename instr_region::JMS_reg>(
                     _sv.v())) {
        const auto &[d_a0] = std::get<typename instr_region::JMS_reg>(_sv.v());
        return f0(d_a0);
      } else {
        return f1;
      }
    }
  };

  struct layout {
    unsigned int base_;
    unsigned int code_;

    __attribute__((pure)) layout *operator->() { return this; }

    __attribute__((pure)) const layout *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) layout clone() const {
      return layout{(*(this)).base_, (*(this)).code_};
    }
  };

  __attribute__((pure)) static bool addr_in_region(const unsigned int &addr,
                                                   const layout &l);
  __attribute__((pure)) static bool in_layout(const layout &l,
                                              const instr_region &i);
  static inline const bool test_region_check =
      in_layout(layout{16u, 32u}, instr_region::jun_reg(40u));

  struct instr_jms {
    // TYPES
    struct JUN_jms {
      unsigned int d_a0;
    };

    struct JMS_jms {
      unsigned int d_a0;
    };

    struct NOP_jms {};

    using variant_t = std::variant<JUN_jms, JMS_jms, NOP_jms>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    instr_jms() {}

    explicit instr_jms(JUN_jms _v) : d_v_(std::move(_v)) {}

    explicit instr_jms(JMS_jms _v) : d_v_(std::move(_v)) {}

    explicit instr_jms(NOP_jms _v) : d_v_(_v) {}

    instr_jms(const instr_jms &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    instr_jms(instr_jms &&_other) : d_v_(std::move(_other.d_v_)) {}

    instr_jms &operator=(const instr_jms &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    instr_jms &operator=(instr_jms &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instr_jms clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<JUN_jms>(_sv.v())) {
        const auto &[d_a0] = std::get<JUN_jms>(_sv.v());
        return instr_jms(JUN_jms{d_a0});
      } else if (std::holds_alternative<JMS_jms>(_sv.v())) {
        const auto &[d_a0] = std::get<JMS_jms>(_sv.v());
        return instr_jms(JMS_jms{d_a0});
      } else {
        return instr_jms(NOP_jms{});
      }
    }

    // CREATORS
    __attribute__((pure)) static instr_jms jun_jms(unsigned int a0) {
      return instr_jms(JUN_jms{std::move(a0)});
    }

    __attribute__((pure)) static instr_jms jms_jms(unsigned int a0) {
      return instr_jms(JMS_jms{std::move(a0)});
    }

    __attribute__((pure)) static instr_jms nop_jms() {
      return instr_jms(NOP_jms{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) instr_jms *operator->() { return this; }

    __attribute__((pure)) const instr_jms *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = instr_jms(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) std::optional<unsigned int> jump_target_jms() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_jms::JUN_jms>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jms::JUN_jms>(_sv.v());
        return std::make_optional<unsigned int>(d_a0);
      } else if (std::holds_alternative<typename instr_jms::JMS_jms>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jms::JMS_jms>(_sv.v());
        return std::make_optional<unsigned int>(d_a0);
      } else {
        return std::optional<unsigned int>();
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 instr_jms_rec(F0 &&f, F1 &&f0, const T1 f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_jms::JUN_jms>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jms::JUN_jms>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename instr_jms::JMS_jms>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jms::JMS_jms>(_sv.v());
        return f0(d_a0);
      } else {
        return f1;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 instr_jms_rect(F0 &&f, F1 &&f0, const T1 f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_jms::JUN_jms>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jms::JUN_jms>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename instr_jms::JMS_jms>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jms::JMS_jms>(_sv.v());
        return f0(d_a0);
      } else {
        return f1;
      }
    }
  };

  __attribute__((pure)) static unsigned int
  option_nat_or_zero(const std::optional<unsigned int> &o);
  static inline const unsigned int test_jms =
      option_nat_or_zero(instr_jms::jms_jms(144u).jump_target_jms());

  struct instr_jun {
    // TYPES
    struct JUN_jun {
      unsigned int d_a0;
    };

    struct JMS_jun {
      unsigned int d_a0;
    };

    struct NOP_jun {};

    using variant_t = std::variant<JUN_jun, JMS_jun, NOP_jun>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    instr_jun() {}

    explicit instr_jun(JUN_jun _v) : d_v_(std::move(_v)) {}

    explicit instr_jun(JMS_jun _v) : d_v_(std::move(_v)) {}

    explicit instr_jun(NOP_jun _v) : d_v_(_v) {}

    instr_jun(const instr_jun &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    instr_jun(instr_jun &&_other) : d_v_(std::move(_other.d_v_)) {}

    instr_jun &operator=(const instr_jun &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    instr_jun &operator=(instr_jun &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instr_jun clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<JUN_jun>(_sv.v())) {
        const auto &[d_a0] = std::get<JUN_jun>(_sv.v());
        return instr_jun(JUN_jun{d_a0});
      } else if (std::holds_alternative<JMS_jun>(_sv.v())) {
        const auto &[d_a0] = std::get<JMS_jun>(_sv.v());
        return instr_jun(JMS_jun{d_a0});
      } else {
        return instr_jun(NOP_jun{});
      }
    }

    // CREATORS
    __attribute__((pure)) static instr_jun jun_jun(unsigned int a0) {
      return instr_jun(JUN_jun{std::move(a0)});
    }

    __attribute__((pure)) static instr_jun jms_jun(unsigned int a0) {
      return instr_jun(JMS_jun{std::move(a0)});
    }

    __attribute__((pure)) static instr_jun nop_jun() {
      return instr_jun(NOP_jun{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) instr_jun *operator->() { return this; }

    __attribute__((pure)) const instr_jun *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = instr_jun(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) std::optional<unsigned int> jump_target_jun() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_jun::JUN_jun>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jun::JUN_jun>(_sv.v());
        return std::make_optional<unsigned int>(d_a0);
      } else if (std::holds_alternative<typename instr_jun::JMS_jun>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jun::JMS_jun>(_sv.v());
        return std::make_optional<unsigned int>(d_a0);
      } else {
        return std::optional<unsigned int>();
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 instr_jun_rec(F0 &&f, F1 &&f0, const T1 f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_jun::JUN_jun>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jun::JUN_jun>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename instr_jun::JMS_jun>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jun::JMS_jun>(_sv.v());
        return f0(d_a0);
      } else {
        return f1;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1>
    T1 instr_jun_rect(F0 &&f, F1 &&f0, const T1 f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_jun::JUN_jun>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jun::JUN_jun>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename instr_jun::JMS_jun>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jun::JMS_jun>(_sv.v());
        return f0(d_a0);
      } else {
        return f1;
      }
    }
  };

  __attribute__((pure)) static unsigned int
  target_default(const std::optional<unsigned int> &o);
  static inline const unsigned int test_jun =
      target_default(instr_jun::jun_jun(511u).jump_target_jun());
  static inline const std::pair<
      std::pair<std::pair<unsigned int, bool>, unsigned int>, unsigned int>
      t = std::make_pair(
          std::make_pair(std::make_pair(test_collection, test_region_check),
                         test_jms),
          test_jun);
};

#endif // INCLUDED_JUMP_TARGETS
