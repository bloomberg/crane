#ifndef INCLUDED_JUMP_TARGETS
#define INCLUDED_JUMP_TARGETS

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                     return (std::move(l_)->length() + 1);
                   }},
        this->v());
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

    // CREATORS
    explicit instr_collection(JUN_coll _v) : d_v_(std::move(_v)) {}

    explicit instr_collection(JMS_coll _v) : d_v_(std::move(_v)) {}

    explicit instr_collection(NOP_coll _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instr_collection> JUN_coll_(unsigned int a0) {
        return std::shared_ptr<instr_collection>(
            new instr_collection(JUN_coll{a0}));
      }

      static std::shared_ptr<instr_collection> JMS_coll_(unsigned int a0) {
        return std::shared_ptr<instr_collection>(
            new instr_collection(JMS_coll{a0}));
      }

      static std::shared_ptr<instr_collection> NOP_coll_() {
        return std::shared_ptr<instr_collection>(
            new instr_collection(NOP_coll{}));
      }

      static std::unique_ptr<instr_collection> JUN_coll_uptr(unsigned int a0) {
        return std::unique_ptr<instr_collection>(
            new instr_collection(JUN_coll{a0}));
      }

      static std::unique_ptr<instr_collection> JMS_coll_uptr(unsigned int a0) {
        return std::unique_ptr<instr_collection>(
            new instr_collection(JMS_coll{a0}));
      }

      static std::unique_ptr<instr_collection> NOP_coll_uptr() {
        return std::unique_ptr<instr_collection>(
            new instr_collection(NOP_coll{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instr_collection_rect(F0 &&f, F1 &&f0, const T1 f1,
                                  const std::shared_ptr<instr_collection> &i) {
    return std::visit(
        Overloaded{[&](const typename instr_collection::JUN_coll _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f(std::move(n));
                   },
                   [&](const typename instr_collection::JMS_coll _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   },
                   [&](const typename instr_collection::NOP_coll _args) -> T1 {
                     return f1;
                   }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instr_collection_rec(F0 &&f, F1 &&f0, const T1 f1,
                                 const std::shared_ptr<instr_collection> &i) {
    return std::visit(
        Overloaded{[&](const typename instr_collection::JUN_coll _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f(std::move(n));
                   },
                   [&](const typename instr_collection::JMS_coll _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   },
                   [&](const typename instr_collection::NOP_coll _args) -> T1 {
                     return f1;
                   }},
        i->v());
  }

  __attribute__((pure)) static std::optional<unsigned int>
  jump_target_collection(const std::shared_ptr<instr_collection> &i);
  static std::shared_ptr<List<unsigned int>> collect_targets(
      const std::shared_ptr<List<std::shared_ptr<instr_collection>>> &prog);
  static inline const unsigned int test_collection =
      collect_targets(
          List<std::shared_ptr<instr_collection>>::ctor::Cons_(
              instr_collection::ctor::JUN_coll_(17u),
              List<std::shared_ptr<instr_collection>>::ctor::Cons_(
                  instr_collection::ctor::NOP_coll_(),
                  List<std::shared_ptr<instr_collection>>::ctor::Cons_(
                      instr_collection::ctor::JMS_coll_(511u),
                      List<std::shared_ptr<instr_collection>>::ctor::Cons_(
                          instr_collection::ctor::NOP_coll_(),
                          List<std::shared_ptr<instr_collection>>::ctor::
                              Nil_())))))
          ->length();

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

    // CREATORS
    explicit instr_region(JUN_reg _v) : d_v_(std::move(_v)) {}

    explicit instr_region(JMS_reg _v) : d_v_(std::move(_v)) {}

    explicit instr_region(NOP_reg _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instr_region> JUN_reg_(unsigned int a0) {
        return std::shared_ptr<instr_region>(new instr_region(JUN_reg{a0}));
      }

      static std::shared_ptr<instr_region> JMS_reg_(unsigned int a0) {
        return std::shared_ptr<instr_region>(new instr_region(JMS_reg{a0}));
      }

      static std::shared_ptr<instr_region> NOP_reg_() {
        return std::shared_ptr<instr_region>(new instr_region(NOP_reg{}));
      }

      static std::unique_ptr<instr_region> JUN_reg_uptr(unsigned int a0) {
        return std::unique_ptr<instr_region>(new instr_region(JUN_reg{a0}));
      }

      static std::unique_ptr<instr_region> JMS_reg_uptr(unsigned int a0) {
        return std::unique_ptr<instr_region>(new instr_region(JMS_reg{a0}));
      }

      static std::unique_ptr<instr_region> NOP_reg_uptr() {
        return std::unique_ptr<instr_region>(new instr_region(NOP_reg{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instr_region_rect(F0 &&f, F1 &&f0, const T1 f1,
                              const std::shared_ptr<instr_region> &i) {
    return std::visit(
        Overloaded{[&](const typename instr_region::JUN_reg _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f(std::move(n));
                   },
                   [&](const typename instr_region::JMS_reg _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   },
                   [&](const typename instr_region::NOP_reg _args) -> T1 {
                     return f1;
                   }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instr_region_rec(F0 &&f, F1 &&f0, const T1 f1,
                             const std::shared_ptr<instr_region> &i) {
    return std::visit(
        Overloaded{[&](const typename instr_region::JUN_reg _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f(std::move(n));
                   },
                   [&](const typename instr_region::JMS_reg _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   },
                   [&](const typename instr_region::NOP_reg _args) -> T1 {
                     return f1;
                   }},
        i->v());
  }

  struct layout {
    unsigned int base_;
    unsigned int code_;
  };

  __attribute__((pure)) static bool
  addr_in_region(const unsigned int addr, const std::shared_ptr<layout> &l);
  __attribute__((pure)) static std::optional<unsigned int>
  jump_target_region(const std::shared_ptr<instr_region> &i);
  __attribute__((pure)) static bool
  in_layout(const std::shared_ptr<layout> &l,
            const std::shared_ptr<instr_region> &i);
  static inline const bool test_region_check =
      in_layout(std::make_shared<layout>(layout{16u, 32u}),
                instr_region::ctor::JUN_reg_(40u));

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

    // CREATORS
    explicit instr_jms(JUN_jms _v) : d_v_(std::move(_v)) {}

    explicit instr_jms(JMS_jms _v) : d_v_(std::move(_v)) {}

    explicit instr_jms(NOP_jms _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instr_jms> JUN_jms_(unsigned int a0) {
        return std::shared_ptr<instr_jms>(new instr_jms(JUN_jms{a0}));
      }

      static std::shared_ptr<instr_jms> JMS_jms_(unsigned int a0) {
        return std::shared_ptr<instr_jms>(new instr_jms(JMS_jms{a0}));
      }

      static std::shared_ptr<instr_jms> NOP_jms_() {
        return std::shared_ptr<instr_jms>(new instr_jms(NOP_jms{}));
      }

      static std::unique_ptr<instr_jms> JUN_jms_uptr(unsigned int a0) {
        return std::unique_ptr<instr_jms>(new instr_jms(JUN_jms{a0}));
      }

      static std::unique_ptr<instr_jms> JMS_jms_uptr(unsigned int a0) {
        return std::unique_ptr<instr_jms>(new instr_jms(JMS_jms{a0}));
      }

      static std::unique_ptr<instr_jms> NOP_jms_uptr() {
        return std::unique_ptr<instr_jms>(new instr_jms(NOP_jms{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instr_jms_rect(F0 &&f, F1 &&f0, const T1 f1,
                           const std::shared_ptr<instr_jms> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instr_jms::JUN_jms _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename instr_jms::JMS_jms _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            },
            [&](const typename instr_jms::NOP_jms _args) -> T1 { return f1; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instr_jms_rec(F0 &&f, F1 &&f0, const T1 f1,
                          const std::shared_ptr<instr_jms> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instr_jms::JUN_jms _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename instr_jms::JMS_jms _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            },
            [&](const typename instr_jms::NOP_jms _args) -> T1 { return f1; }},
        i->v());
  }

  __attribute__((pure)) static std::optional<unsigned int>
  jump_target_jms(const std::shared_ptr<instr_jms> &i);
  __attribute__((pure)) static unsigned int
  option_nat_or_zero(const std::optional<unsigned int> o);
  static inline const unsigned int test_jms =
      option_nat_or_zero(jump_target_jms(instr_jms::ctor::JMS_jms_(144u)));

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

    // CREATORS
    explicit instr_jun(JUN_jun _v) : d_v_(std::move(_v)) {}

    explicit instr_jun(JMS_jun _v) : d_v_(std::move(_v)) {}

    explicit instr_jun(NOP_jun _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instr_jun> JUN_jun_(unsigned int a0) {
        return std::shared_ptr<instr_jun>(new instr_jun(JUN_jun{a0}));
      }

      static std::shared_ptr<instr_jun> JMS_jun_(unsigned int a0) {
        return std::shared_ptr<instr_jun>(new instr_jun(JMS_jun{a0}));
      }

      static std::shared_ptr<instr_jun> NOP_jun_() {
        return std::shared_ptr<instr_jun>(new instr_jun(NOP_jun{}));
      }

      static std::unique_ptr<instr_jun> JUN_jun_uptr(unsigned int a0) {
        return std::unique_ptr<instr_jun>(new instr_jun(JUN_jun{a0}));
      }

      static std::unique_ptr<instr_jun> JMS_jun_uptr(unsigned int a0) {
        return std::unique_ptr<instr_jun>(new instr_jun(JMS_jun{a0}));
      }

      static std::unique_ptr<instr_jun> NOP_jun_uptr() {
        return std::unique_ptr<instr_jun>(new instr_jun(NOP_jun{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instr_jun_rect(F0 &&f, F1 &&f0, const T1 f1,
                           const std::shared_ptr<instr_jun> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instr_jun::JUN_jun _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename instr_jun::JMS_jun _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            },
            [&](const typename instr_jun::NOP_jun _args) -> T1 { return f1; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instr_jun_rec(F0 &&f, F1 &&f0, const T1 f1,
                          const std::shared_ptr<instr_jun> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instr_jun::JUN_jun _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename instr_jun::JMS_jun _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            },
            [&](const typename instr_jun::NOP_jun _args) -> T1 { return f1; }},
        i->v());
  }

  __attribute__((pure)) static std::optional<unsigned int>
  jump_target_jun(const std::shared_ptr<instr_jun> &i);
  __attribute__((pure)) static unsigned int
  target_default(const std::optional<unsigned int> o);
  static inline const unsigned int test_jun =
      target_default(jump_target_jun(instr_jun::ctor::JUN_jun_(511u)));
  static inline const std::pair<
      std::pair<std::pair<unsigned int, bool>, unsigned int>, unsigned int>
      t = std::make_pair(
          std::make_pair(std::make_pair(test_collection, test_region_check),
                         test_jms),
          test_jun);
};

#endif // INCLUDED_JUMP_TARGETS
