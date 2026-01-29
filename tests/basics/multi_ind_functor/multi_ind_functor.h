#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename M>
concept Elem = requires {
  typename M::t;
  requires std::same_as<std::remove_cvref_t<decltype(M::dflt)>, typename M::t>;
};

template <Elem E> struct Container {
  struct maybe {
  public:
    struct Nothing {};
    struct Just {
      unsigned int _a0;
    };
    using variant_t = std::variant<Nothing, Just>;

  private:
    variant_t v_;
    explicit maybe(Nothing _v) : v_(std::move(_v)) {}
    explicit maybe(Just _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<maybe> Nothing_() {
        return std::shared_ptr<maybe>(new maybe(Nothing{}));
      }
      static std::shared_ptr<maybe> Just_(unsigned int a0) {
        return std::shared_ptr<maybe>(new maybe(Just{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 maybe_rect(const T1 f, F1 &&f0, const std::shared_ptr<maybe> &m) {
    return std::visit(
        Overloaded{[&](const typename maybe::Nothing _args) -> T1 { return f; },
                   [&](const typename maybe::Just _args) -> T1 {
                     unsigned int n = _args._a0;
                     return f0(n);
                   }},
        m->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 maybe_rec(const T1 f, F1 &&f0, const std::shared_ptr<maybe> &m) {
    return std::visit(
        Overloaded{[&](const typename maybe::Nothing _args) -> T1 { return f; },
                   [&](const typename maybe::Just _args) -> T1 {
                     unsigned int n = _args._a0;
                     return f0(n);
                   }},
        m->v());
  }

  struct mlist {
  public:
    struct MNil {};
    struct MCons {
      std::shared_ptr<maybe> _a0;
      std::shared_ptr<mlist> _a1;
    };
    using variant_t = std::variant<MNil, MCons>;

  private:
    variant_t v_;
    explicit mlist(MNil _v) : v_(std::move(_v)) {}
    explicit mlist(MCons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<mlist> MNil_() {
        return std::shared_ptr<mlist>(new mlist(MNil{}));
      }
      static std::shared_ptr<mlist> MCons_(const std::shared_ptr<maybe> &a0,
                                           const std::shared_ptr<mlist> &a1) {
        return std::shared_ptr<mlist>(new mlist(MCons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1,
            MapsTo<T1, std::shared_ptr<maybe>, std::shared_ptr<mlist>, T1> F1>
  static T1 mlist_rect(const T1 f, F1 &&f0, const std::shared_ptr<mlist> &m) {
    return std::visit(
        Overloaded{[&](const typename mlist::MNil _args) -> T1 { return f; },
                   [&](const typename mlist::MCons _args) -> T1 {
                     std::shared_ptr<maybe> m0 = _args._a0;
                     std::shared_ptr<mlist> m1 = _args._a1;
                     return f0(m0, m1, mlist_rect<T1>(f, f0, m1));
                   }},
        m->v());
  }

  template <typename T1,
            MapsTo<T1, std::shared_ptr<maybe>, std::shared_ptr<mlist>, T1> F1>
  static T1 mlist_rec(const T1 f, F1 &&f0, const std::shared_ptr<mlist> &m) {
    return std::visit(
        Overloaded{[&](const typename mlist::MNil _args) -> T1 { return f; },
                   [&](const typename mlist::MCons _args) -> T1 {
                     std::shared_ptr<maybe> m0 = _args._a0;
                     std::shared_ptr<mlist> m1 = _args._a1;
                     return f0(m0, m1, mlist_rec<T1>(f, f0, m1));
                   }},
        m->v());
  }

  struct mtree {
  public:
    struct Leaf {
      std::shared_ptr<maybe> _a0;
    };
    struct Node {
      std::shared_ptr<mlist> _a0;
    };
    using variant_t = std::variant<Leaf, Node>;

  private:
    variant_t v_;
    explicit mtree(Leaf _v) : v_(std::move(_v)) {}
    explicit mtree(Node _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<mtree> Leaf_(const std::shared_ptr<maybe> &a0) {
        return std::shared_ptr<mtree>(new mtree(Leaf{a0}));
      }
      static std::shared_ptr<mtree> Node_(const std::shared_ptr<mlist> &a0) {
        return std::shared_ptr<mtree>(new mtree(Node{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<maybe>> F0,
            MapsTo<T1, std::shared_ptr<mlist>> F1>
  static T1 mtree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<mtree> &m) {
    return std::visit(Overloaded{[&](const typename mtree::Leaf _args) -> T1 {
                                   std::shared_ptr<maybe> m0 = _args._a0;
                                   return f(m0);
                                 },
                                 [&](const typename mtree::Node _args) -> T1 {
                                   std::shared_ptr<mlist> m0 = _args._a0;
                                   return f0(m0);
                                 }},
                      m->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<maybe>> F0,
            MapsTo<T1, std::shared_ptr<mlist>> F1>
  static T1 mtree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<mtree> &m) {
    return std::visit(Overloaded{[&](const typename mtree::Leaf _args) -> T1 {
                                   std::shared_ptr<maybe> m0 = _args._a0;
                                   return f(m0);
                                 },
                                 [&](const typename mtree::Node _args) -> T1 {
                                   std::shared_ptr<mlist> m0 = _args._a0;
                                   return f0(m0);
                                 }},
                      m->v());
  }

  static bool is_nothing(const std::shared_ptr<maybe> &m) {
    return std::visit(
        Overloaded{
            [](const typename maybe::Nothing _args) -> bool { return true; },
            [](const typename maybe::Just _args) -> bool { return false; }},
        m->v());
  }

  static unsigned int mlist_length(const std::shared_ptr<mlist> &l) {
    return std::visit(
        Overloaded{
            [](const typename mlist::MNil _args) -> unsigned int { return 0; },
            [](const typename mlist::MCons _args) -> unsigned int {
              std::shared_ptr<mlist> rest = _args._a1;
              return (mlist_length(rest) + 1);
            }},
        l->v());
  }

  static unsigned int tree_size(const std::shared_ptr<mtree> &t0) {
    return std::visit(
        Overloaded{[](const typename mtree::Leaf _args) -> unsigned int {
                     std::shared_ptr<maybe> m = _args._a0;
                     if (is_nothing(m)) {
                       return 0;
                     } else {
                       return (0 + 1);
                     }
                   },
                   [](const typename mtree::Node _args) -> unsigned int {
                     std::shared_ptr<mlist> children = _args._a0;
                     return mlist_length(children);
                   }},
        t0->v());
  }

  static inline std::shared_ptr<maybe> empty_maybe = maybe::ctor::Nothing_();

  static inline std::shared_ptr<maybe> some_val = maybe::ctor::Just_((
      (((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
                                         1) +
                                        1) +
                                       1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1) +
       1) +
      1));

  static inline std::shared_ptr<mlist> sample_list = mlist::ctor::MCons_(
      maybe::ctor::Just_(
          ((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) +
                                               1) +
                                              1) +
                                             1) +
                                            1) +
                                           1) +
                                          1) +
                                         1) +
                                        1) +
                                       1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1)),
      mlist::ctor::MCons_(maybe::ctor::Nothing_(), mlist::ctor::MNil_()));

  static inline std::shared_ptr<mtree> sample_tree =
      mtree::ctor::Node_(sample_list);
};

struct NatElem {
  using t = unsigned int;

  static inline const unsigned int dflt =
      ((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) +
                                           1) +
                                          1) +
                                         1) +
                                        1) +
                                       1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1) +
       1);
};
static_assert(Elem<NatElem>);

using NatContainer = Container<NatElem>;

const bool test_is_nothing =
    NatContainer::is_nothing(NatContainer::empty_maybe);

const unsigned int test_list_len =
    NatContainer::mlist_length(NatContainer::sample_list);

const unsigned int test_tree_size =
    NatContainer::tree_size(NatContainer::sample_tree);
