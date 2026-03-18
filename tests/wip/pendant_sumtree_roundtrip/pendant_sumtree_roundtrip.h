#ifndef INCLUDED_PENDANT_SUMTREE_ROUNDTRIP
#define INCLUDED_PENDANT_SUMTREE_ROUNDTRIP

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil0 {};

  struct Cons0 {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil0, Cons0>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil0 _v) : d_v_(std::move(_v)) {}

  explicit List(Cons0 _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil0_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil0{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons0_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons0{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil0_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil0{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons0_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons0{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bool forallb(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil0 _args) -> bool { return true; },
            [&](const typename List<t_A>::Cons0 _args) -> bool {
              return (f(_args.d_a0) && _args.d_a1->forallb(f));
            }},
        this->v());
  }

  template <typename T1, MapsTo<T1, t_A, T1> F0>
  T1 fold_right(F0 &&f, const T1 a0) const {
    return std::visit(
        Overloaded{
            [&](const typename List<t_A>::Nil0 _args) -> T1 { return a0; },
            [&](const typename List<t_A>::Cons0 _args) -> T1 {
              return f(_args.d_a0, _args.d_a1->template fold_right<T1>(f, a0));
            }},
        this->v());
  }

  template <typename T1> std::shared_ptr<List<T1>> concat() const {
    return std::visit(
        Overloaded{
            [](const typename List<std::shared_ptr<List<T1>>>::Nil0 _args)
                -> std::shared_ptr<List<T1>> {
              return List<T1>::ctor::Nil0_();
            },
            [](const typename List<std::shared_ptr<List<T1>>>::Cons0 _args)
                -> std::shared_ptr<List<T1>> {
              return _args.d_a0->app(_args.d_a1->template concat<T1>());
            }},
        this->v());
  }

  template <typename T1, MapsTo<T1, t_A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    return std::visit(Overloaded{[](const typename List<t_A>::Nil0 _args)
                                     -> std::shared_ptr<List<T1>> {
                                   return List<T1>::ctor::Nil0_();
                                 },
                                 [&](const typename List<t_A>::Cons0 _args)
                                     -> std::shared_ptr<List<T1>> {
                                   return List<T1>::ctor::Cons0_(
                                       f(_args.d_a0),
                                       _args.d_a1->template map<T1>(f));
                                 }},
                      this->v());
  }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil0 _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons0 _args) -> unsigned int {
                     return (_args.d_a1->length() + 1);
                   }},
        this->v());
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    return std::visit(
        Overloaded{[&](const typename List<t_A>::Nil0 _args)
                       -> std::shared_ptr<List<t_A>> { return m; },
                   [&](const typename List<t_A>::Cons0 _args)
                       -> std::shared_ptr<List<t_A>> {
                     return List<t_A>::ctor::Cons0_(_args.d_a0,
                                                    _args.d_a1->app(m));
                   }},
        this->v());
  }
};

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_a0;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Sig<t_A>> Exist_(t_A a0) {
      return std::shared_ptr<Sig<t_A>>(new Sig<t_A>(Exist{a0}));
    }

    static std::unique_ptr<Sig<t_A>> Exist_uptr(t_A a0) {
      return std::unique_ptr<Sig<t_A>>(new Sig<t_A>(Exist{a0}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A, typename t_P> struct SigT {
  // TYPES
  struct ExistT {
    t_A d_a0;
    t_P d_a1;
  };

  using variant_t = std::variant<ExistT>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit SigT(ExistT _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<SigT<t_A, t_P>> ExistT_(t_A a0, t_P a1) {
      return std::shared_ptr<SigT<t_A, t_P>>(
          new SigT<t_A, t_P>(ExistT{a0, a1}));
    }

    static std::unique_ptr<SigT<t_A, t_P>> ExistT_uptr(t_A a0, t_P a1) {
      return std::unique_ptr<SigT<t_A, t_P>>(
          new SigT<t_A, t_P>(ExistT{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct PeanoNat {
  __attribute__((pure)) static bool eqb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static unsigned int max(const unsigned int n,
                                                const unsigned int m);
};

template <typename t_A> struct T0 {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    unsigned int d_a1;
    std::shared_ptr<T0<t_A>> d_a2;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit T0(Nil _v) : d_v_(std::move(_v)) {}

  explicit T0(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<T0<t_A>> Nil_() {
      return std::shared_ptr<T0<t_A>>(new T0<t_A>(Nil{}));
    }

    static std::shared_ptr<T0<t_A>> Cons_(t_A a0, unsigned int a1,
                                          const std::shared_ptr<T0<t_A>> &a2) {
      return std::shared_ptr<T0<t_A>>(new T0<t_A>(Cons{a0, a1, a2}));
    }

    static std::unique_ptr<T0<t_A>> Nil_uptr() {
      return std::unique_ptr<T0<t_A>>(new T0<t_A>(Nil{}));
    }

    static std::unique_ptr<T0<t_A>>
    Cons_uptr(t_A a0, unsigned int a1, const std::shared_ptr<T0<t_A>> &a2) {
      return std::unique_ptr<T0<t_A>>(new T0<t_A>(Cons{a0, a1, a2}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct T {
  // TYPES
  struct F1 {
    unsigned int d_a0;
  };

  struct FS {
    unsigned int d_a0;
    std::shared_ptr<T> d_a1;
  };

  using variant_t = std::variant<F1, FS>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit T(F1 _v) : d_v_(std::move(_v)) {}

  explicit T(FS _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<T> F1_(unsigned int a0) {
      return std::shared_ptr<T>(new T(F1{a0}));
    }

    static std::shared_ptr<T> FS_(unsigned int a0,
                                  const std::shared_ptr<T> &a1) {
      return std::shared_ptr<T>(new T(FS{a0, a1}));
    }

    static std::unique_ptr<T> F1_uptr(unsigned int a0) {
      return std::unique_ptr<T>(new T(F1{a0}));
    }

    static std::unique_ptr<T> FS_uptr(unsigned int a0,
                                      const std::shared_ptr<T> &a1) {
      return std::unique_ptr<T>(new T(FS{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<Sig<unsigned int>> to_nat(const unsigned int _x) const {
    return std::visit(
        Overloaded{
            [](const typename T::F1 _args)
                -> std::shared_ptr<Sig<unsigned int>> {
              return Sig<unsigned int>::ctor::Exist_(0u);
            },
            [](const typename T::FS _args)
                -> std::shared_ptr<Sig<unsigned int>> {
              return std::visit(
                  Overloaded{[](const typename Sig<unsigned int>::Exist _args0)
                                 -> std::shared_ptr<Sig<unsigned int>> {
                    return Sig<unsigned int>::ctor::Exist_((_args0.d_a0 + 1));
                  }},
                  _args.d_a1->to_nat(_args.d_a0)->v());
            }},
        this->v());
  }
};

struct Fin {
  static std::shared_ptr<T> of_nat_lt(const unsigned int p,
                                      const unsigned int n);
};

struct Vector {
  template <typename T1>
  static std::shared_ptr<List<T1>> to_list(const unsigned int n,
                                           const std::shared_ptr<T0<T1>> &v);
};

struct Datatypes {
  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static std::optional<T2>
  option_map(F0 &&f, const std::optional<T1> o);
};

struct PendantSumtreeRoundtripCase {
  using digit = std::shared_ptr<T>;
  __attribute__((pure)) static unsigned int
  digit_to_nat(const std::shared_ptr<T> &d);
  __attribute__((pure)) static digit digit_of_nat(const unsigned int n);
  static inline const digit digit0 = digit_of_nat(0u);
  static inline const digit digit1 = digit_of_nat(1u);
  static inline const digit digit2 = digit_of_nat(2u);
  static inline const digit digit3 = digit_of_nat(3u);
  static inline const digit digit4 = digit_of_nat(4u);
  static inline const digit digit5 = digit_of_nat(5u);
  static inline const digit digit6 = digit_of_nat(6u);
  static inline const digit digit7 = digit_of_nat(7u);
  static inline const digit digit9 = digit_of_nat(9u);
  __attribute__((pure)) static unsigned int
  value_digits(const unsigned int _x,
               const std::shared_ptr<T0<std::shared_ptr<T>>> &ds);
  __attribute__((pure)) static std::optional<std::shared_ptr<T0<digit>>>
  list_to_vector_opt(const unsigned int n,
                     const std::shared_ptr<List<std::shared_ptr<T>>> &xs);
  static std::shared_ptr<List<std::shared_ptr<List<digit>>>> encode_multi(
      const unsigned int n,
      const std::shared_ptr<List<std::shared_ptr<T0<std::shared_ptr<T>>>>>
          &nums);
  __attribute__((pure)) static std::optional<
      std::shared_ptr<List<std::shared_ptr<T0<digit>>>>>
  decode_multi(
      const unsigned int n,
      const std::shared_ptr<List<std::shared_ptr<List<std::shared_ptr<T>>>>>
          &segments);
  enum class Twist { e_TS, e_TZ };

  template <typename T1>
  static T1 Twist_rect(const T1 f, const T1 f0, const Twist t1) {
    return [&](void) {
      switch (t1) {
      case Twist::e_TS: {
        return f;
      }
      case Twist::e_TZ: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 Twist_rec(const T1 f, const T1 f0, const Twist t1) {
    return [&](void) {
      switch (t1) {
      case Twist::e_TS: {
        return f;
      }
      case Twist::e_TZ: {
        return f0;
      }
      }
    }();
  }
  enum class Fiber { e_COTTON, e_CAMELID };

  template <typename T1>
  static T1 Fiber_rect(const T1 f, const T1 f0, const Fiber f1) {
    return [&](void) {
      switch (f1) {
      case Fiber::e_COTTON: {
        return f;
      }
      case Fiber::e_CAMELID: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 Fiber_rec(const T1 f, const T1 f0, const Fiber f1) {
    return [&](void) {
      switch (f1) {
      case Fiber::e_COTTON: {
        return f;
      }
      case Fiber::e_CAMELID: {
        return f0;
      }
      }
    }();
  }
  enum class Color { e_WHITE, e_BROWN, e_RED, e_BLUE };

  template <typename T1>
  static T1 Color_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                       const Color c) {
    return [&](void) {
      switch (c) {
      case Color::e_WHITE: {
        return f;
      }
      case Color::e_BROWN: {
        return f0;
      }
      case Color::e_RED: {
        return f1;
      }
      case Color::e_BLUE: {
        return f2;
      }
      }
    }();
  }

  template <typename T1>
  static T1 Color_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                      const Color c) {
    return [&](void) {
      switch (c) {
      case Color::e_WHITE: {
        return f;
      }
      case Color::e_BROWN: {
        return f0;
      }
      case Color::e_RED: {
        return f1;
      }
      case Color::e_BLUE: {
        return f2;
      }
      }
    }();
  }

  struct CordMeta {
    Fiber cm_fiber;
    Color cm_color;
    Twist cm_spin;
    Twist cm_ply;
  };

  struct CertifiedPendant {
    std::shared_ptr<CordMeta> cp_meta;
    std::shared_ptr<T0<digit>> cp_digits;
  };

  __attribute__((pure)) static std::optional<std::shared_ptr<T0<digit>>>
  pendant_digits(const unsigned int n, std::shared_ptr<CertifiedPendant> p);
  __attribute__((pure)) static std::optional<unsigned int>
  pendant_value(const unsigned int n,
                const std::shared_ptr<CertifiedPendant> &p);
  using Ledger = std::shared_ptr<List<
      std::shared_ptr<SigT<unsigned int, std::shared_ptr<CertifiedPendant>>>>>;
  static std::shared_ptr<List<std::optional<unsigned int>>> ledger_values(
      const std::shared_ptr<List<std::shared_ptr<
          SigT<unsigned int, std::shared_ptr<CertifiedPendant>>>>> &l);

  struct PendantGroup {
    std::shared_ptr<CertifiedPendant> pg_top;
    std::shared_ptr<List<std::shared_ptr<CertifiedPendant>>> pg_pendants;
  };

  __attribute__((pure)) static bool
  group_sums_validb(const unsigned int n,
                    const std::shared_ptr<PendantGroup> &g);

  struct SumTree {
    // TYPES
    struct SumLeaf {
      std::shared_ptr<CertifiedPendant> d_a0;
    };

    struct SumNode {
      std::shared_ptr<CertifiedPendant> d_a0;
      std::shared_ptr<List<std::shared_ptr<SumTree>>> d_a1;
    };

    using variant_t = std::variant<SumLeaf, SumNode>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit SumTree(SumLeaf _v) : d_v_(std::move(_v)) {}

    explicit SumTree(SumNode _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<SumTree>
      SumLeaf_(const std::shared_ptr<CertifiedPendant> &a0) {
        return std::shared_ptr<SumTree>(new SumTree(SumLeaf{a0}));
      }

      static std::shared_ptr<SumTree>
      SumNode_(const std::shared_ptr<CertifiedPendant> &a0,
               const std::shared_ptr<List<std::shared_ptr<SumTree>>> &a1) {
        return std::shared_ptr<SumTree>(new SumTree(SumNode{a0, a1}));
      }

      static std::unique_ptr<SumTree>
      SumLeaf_uptr(const std::shared_ptr<CertifiedPendant> &a0) {
        return std::unique_ptr<SumTree>(new SumTree(SumLeaf{a0}));
      }

      static std::unique_ptr<SumTree>
      SumNode_uptr(const std::shared_ptr<CertifiedPendant> &a0,
                   const std::shared_ptr<List<std::shared_ptr<SumTree>>> &a1) {
        return std::unique_ptr<SumTree>(new SumTree(SumNode{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<CertifiedPendant>> F1,
            MapsTo<T1, std::shared_ptr<CertifiedPendant>,
                   std::shared_ptr<List<std::shared_ptr<SumTree>>>>
                F2>
  static T1 SumTree_rect(const unsigned int _x, F1 &&f, F2 &&f0,
                         const std::shared_ptr<SumTree> &s) {
    return std::visit(
        Overloaded{[&](const typename SumTree::SumLeaf _args) -> T1 {
                     return f(_args.d_a0);
                   },
                   [&](const typename SumTree::SumNode _args) -> T1 {
                     return f0(_args.d_a0, _args.d_a1);
                   }},
        s->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<CertifiedPendant>> F1,
            MapsTo<T1, std::shared_ptr<CertifiedPendant>,
                   std::shared_ptr<List<std::shared_ptr<SumTree>>>>
                F2>
  static T1 SumTree_rec(const unsigned int _x, F1 &&f, F2 &&f0,
                        const std::shared_ptr<SumTree> &s) {
    return std::visit(
        Overloaded{[&](const typename SumTree::SumLeaf _args) -> T1 {
                     return f(_args.d_a0);
                   },
                   [&](const typename SumTree::SumNode _args) -> T1 {
                     return f0(_args.d_a0, _args.d_a1);
                   }},
        s->v());
  }

  static std::shared_ptr<CertifiedPendant>
  sumtree_top(const unsigned int _x, const std::shared_ptr<SumTree> &st);
  static std::shared_ptr<List<std::shared_ptr<CertifiedPendant>>>
  sumtree_leaves(const unsigned int n, const std::shared_ptr<SumTree> &st);
  __attribute__((pure)) static unsigned int
  sumtree_depth(const unsigned int n, const std::shared_ptr<SumTree> &st);
  __attribute__((pure)) static bool
  sumtree_validb_aux(const unsigned int n, const unsigned int fuel,
                     const std::shared_ptr<SumTree> &st);
  __attribute__((pure)) static bool
  sumtree_validb(const unsigned int n, const std::shared_ptr<SumTree> &st);
  __attribute__((pure)) static std::optional<unsigned int>
  sumtree_leaf_total(const unsigned int n, const std::shared_ptr<SumTree> &st);
  __attribute__((pure)) static bool
  nat_list_eqb(const std::shared_ptr<List<unsigned int>> &xs,
               const std::shared_ptr<List<unsigned int>> &ys);
  __attribute__((pure)) static bool
  option_nat_eqb(const std::optional<unsigned int> x,
                 const std::optional<unsigned int> y);
  __attribute__((pure)) static bool
  option_nat_is_some(const std::optional<unsigned int> x);
  static std::shared_ptr<T0<digit>> digit_vec1(std::shared_ptr<T> a);
  static std::shared_ptr<T0<digit>>
  digit_vec3(std::shared_ptr<T> a, std::shared_ptr<T> b, std::shared_ptr<T> c);
  static inline const std::shared_ptr<CordMeta> sample_meta_a =
      std::make_shared<CordMeta>(
          CordMeta{Fiber::e_COTTON, Color::e_BROWN, Twist::e_TS, Twist::e_TZ});
  static inline const std::shared_ptr<CordMeta> sample_meta_b =
      std::make_shared<CordMeta>(
          CordMeta{Fiber::e_CAMELID, Color::e_RED, Twist::e_TZ, Twist::e_TS});
  static inline const std::shared_ptr<CordMeta> sample_meta_c =
      std::make_shared<CordMeta>(
          CordMeta{Fiber::e_COTTON, Color::e_BLUE, Twist::e_TS, Twist::e_TS});
  static inline const std::shared_ptr<T0<digit>> digits_731 =
      digit_vec3(digit1, digit3, digit7);
  static inline const std::shared_ptr<T0<digit>> digits_462 =
      digit_vec3(digit2, digit6, digit4);
  static inline const std::shared_ptr<T0<digit>> digits_269 =
      digit_vec3(digit9, digit6, digit2);
  static inline const std::shared_ptr<T0<digit>> digits_200 =
      digit_vec3(digit0, digit0, digit2);
  static inline const std::shared_ptr<T0<digit>> digits_069 =
      digit_vec3(digit9, digit6, digit0);
  static inline const std::shared_ptr<T0<digit>> digits_5 = digit_vec1(digit5);
  static inline const std::shared_ptr<CertifiedPendant> pendant_731 =
      std::make_shared<CertifiedPendant>(
          CertifiedPendant{sample_meta_a, digits_731});
  static inline const std::shared_ptr<CertifiedPendant> pendant_462 =
      std::make_shared<CertifiedPendant>(
          CertifiedPendant{sample_meta_b, digits_462});
  static inline const std::shared_ptr<CertifiedPendant> pendant_269 =
      std::make_shared<CertifiedPendant>(
          CertifiedPendant{sample_meta_c, digits_269});
  static inline const std::shared_ptr<CertifiedPendant> pendant_200 =
      std::make_shared<CertifiedPendant>(
          CertifiedPendant{sample_meta_b, digits_200});
  static inline const std::shared_ptr<CertifiedPendant> pendant_069 =
      std::make_shared<CertifiedPendant>(
          CertifiedPendant{sample_meta_c, digits_069});
  static inline const std::shared_ptr<CertifiedPendant> pendant_5 =
      std::make_shared<CertifiedPendant>(
          CertifiedPendant{sample_meta_a, digits_5});
  static inline const std::shared_ptr<List<std::shared_ptr<T0<digit>>>>
      sample_multi_digits =
          List<std::shared_ptr<T0<std::shared_ptr<T>>>>::ctor::Cons0_(
              digits_731,
              List<std::shared_ptr<T0<std::shared_ptr<T>>>>::ctor::Cons0_(
                  digits_462,
                  List<std::shared_ptr<T0<std::shared_ptr<T>>>>::ctor::Cons0_(
                      digits_269,
                      List<std::shared_ptr<T0<std::shared_ptr<T>>>>::ctor::
                          Nil0_())));
  static inline const bool sample_multi_roundtrip_ok = [](void) {
    if (decode_multi(3u, encode_multi(3u, sample_multi_digits)).has_value()) {
      std::shared_ptr<List<std::shared_ptr<T0<std::shared_ptr<T>>>>> decoded =
          *decode_multi(3u, encode_multi(3u, sample_multi_digits));
      return nat_list_eqb(
          std::move(decoded)->template map<unsigned int>(
              [](const std::shared_ptr<T0<digit>> &_x0) -> unsigned int {
                return value_digits(3u, _x0);
              }),
          List<unsigned int>::ctor::Cons0_(
              731u, List<unsigned int>::ctor::Cons0_(
                        462u, List<unsigned int>::ctor::Cons0_(
                                  269u, List<unsigned int>::ctor::Nil0_()))));
    } else {
      return false;
    }
  }();
  static inline const std::shared_ptr<PendantGroup> sample_group =
      std::make_shared<PendantGroup>(PendantGroup{
          pendant_731,
          List<std::shared_ptr<CertifiedPendant>>::ctor::Cons0_(
              pendant_462,
              List<std::shared_ptr<CertifiedPendant>>::ctor::Cons0_(
                  pendant_269,
                  List<std::shared_ptr<CertifiedPendant>>::ctor::Nil0_()))});
  static inline const std::shared_ptr<SumTree> sample_subtree =
      SumTree::ctor::SumNode_(
          pendant_269, List<std::shared_ptr<SumTree>>::ctor::Cons0_(
                           SumTree::ctor::SumLeaf_(pendant_200),
                           List<std::shared_ptr<SumTree>>::ctor::Cons0_(
                               SumTree::ctor::SumLeaf_(pendant_069),
                               List<std::shared_ptr<SumTree>>::ctor::Nil0_())));
  static inline const std::shared_ptr<SumTree> sample_tree =
      SumTree::ctor::SumNode_(
          pendant_731, List<std::shared_ptr<SumTree>>::ctor::Cons0_(
                           SumTree::ctor::SumLeaf_(pendant_462),
                           List<std::shared_ptr<SumTree>>::ctor::Cons0_(
                               sample_subtree,
                               List<std::shared_ptr<SumTree>>::ctor::Nil0_())));
  static inline const Ledger sample_ledger = List<
      std::shared_ptr<SigT<unsigned int, std::shared_ptr<CertifiedPendant>>>>::
      ctor::Cons0_(
          SigT<unsigned int, std::shared_ptr<CertifiedPendant>>::ctor::ExistT_(
              3u, pendant_731),
          List<std::shared_ptr<
              SigT<unsigned int, std::shared_ptr<CertifiedPendant>>>>::ctor::
              Cons0_(
                  SigT<unsigned int, std::shared_ptr<CertifiedPendant>>::ctor::
                      ExistT_(3u, pendant_462),
                  List<std::shared_ptr<
                      SigT<unsigned int, std::shared_ptr<CertifiedPendant>>>>::
                      ctor::Cons0_(
                          SigT<unsigned int,
                               std::shared_ptr<CertifiedPendant>>::ctor::
                              ExistT_(1u, pendant_5),
                          List<std::shared_ptr<
                              SigT<unsigned int,
                                   std::shared_ptr<CertifiedPendant>>>>::ctor::
                              Nil0_())));
  static inline const bool sample_group_valid =
      group_sums_validb(3u, sample_group);
  static inline const bool sample_subtree_valid =
      sumtree_validb(3u, sample_subtree);
  static inline const bool sample_tree_valid = sumtree_validb(3u, sample_tree);
  static inline const bool sample_leaf_total_matches_root = option_nat_eqb(
      sumtree_leaf_total(3u, sample_tree), pendant_value(3u, pendant_731));
  static inline const unsigned int sample_tree_depth =
      sumtree_depth(3u, sample_tree);
  static inline const unsigned int sample_ledger_entry_count =
      ledger_values(sample_ledger)->length();
  static inline const bool sample_ledger_all_present =
      ledger_values(sample_ledger)->forallb(option_nat_is_some);
};

template <typename T1, typename T2, MapsTo<T2, T1> F0>
__attribute__((pure)) std::optional<T2>
Datatypes::option_map(F0 &&f, const std::optional<T1> o) {
  if (o.has_value()) {
    T1 a = *o;
    return std::make_optional<T2>(f(a));
  } else {
    return std::nullopt;
  }
}

template <typename T1>
std::shared_ptr<List<T1>> Vector::to_list(const unsigned int n,
                                          const std::shared_ptr<T0<T1>> &v) {
  std::function<std::shared_ptr<List<T1>>(unsigned int, std::shared_ptr<T0<T1>>,
                                          std::shared_ptr<List<T1>>)>
      fold_right_fix;
  fold_right_fix =
      [&](unsigned int _x, std::shared_ptr<T0<T1>> v0,
          std::shared_ptr<List<T1>> b) -> std::shared_ptr<List<T1>> {
    return std::visit(
        Overloaded{[&](const typename T0<T1>::Nil _args)
                       -> std::shared_ptr<List<T1>> { return std::move(b); },
                   [&](const typename T0<T1>::Cons _args)
                       -> std::shared_ptr<List<T1>> {
                     return List<T1>::ctor::Cons0_(
                         _args.d_a0,
                         fold_right_fix(_args.d_a1, _args.d_a2, std::move(b)));
                   }},
        v0->v());
  };
  return fold_right_fix(n, v, List<T1>::ctor::Nil0_());
}

#endif // INCLUDED_PENDANT_SUMTREE_ROUNDTRIP
