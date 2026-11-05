#ifndef INCLUDED_BOXED_ELEMENT_CONCEPT
#define INCLUDED_BOXED_ELEMENT_CONCEPT

#include <concepts>
#include <conslist.h>
#include <cstdint>
#include <type_traits>
#include <utility>
#include <variant>

struct Datatypes {
  template <typename T1>
  static crane::list<T1> app(const crane::list<T1> &l, crane::list<T1> m);
};

struct List {
  template <typename T1, typename T2, typename F0>
  static crane::list<T2> flat_map(F0 &&f, const crane::list<T1> &l);
  template <typename T1, typename T2, typename F0>
  static T1 fold_left(F0 &&f, const crane::list<T2> &l, T1 a0);
};

/// A module type naming a mapped container of an element that recurses
/// through it, under a Boxed Element wrapper: the module's struct holds
/// crane::list<crane::box<rose>>, so the concept the module type becomes
/// has to ask for that type too, the element hole decided as everywhere
/// else, or the module satisfying the module type does not satisfy the
/// concept: children's result is asked for by std::same_as.
struct BoxedElementConcept {
  struct rose {
    // TYPES
    struct Node {
      uint64_t n;
      crane::list<crane::box<rose>> kids;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(Node _v) : v_(std::move(_v)) {}

    static rose node(uint64_t n, crane::list<crane::box<rose>> kids) {
      return rose(Node{n, std::move(kids)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &,
                                   const crane::list<crane::box<rose>> &>
  static T1 rose_rect(F0 &&f, const rose &r) {
    const auto &[n0, kids0] = std::get<typename rose::Node>(r.v());
    return f(n0, kids0);
  }

  template <typename T1, typename F0>
  static T1 rose_rec(F0 &&f, const rose &r) {
    return rose_rect<T1>(f, r);
  }

  static uint64_t size(const rose &r);

  struct Forest {
    static inline const crane::list<crane::box<rose>> forest = crane::cons(
        rose::node(UINT64_C(1), crane::list<crane::box<rose>>{}),
        crane::cons(
            rose::node(UINT64_C(2),
                       crane::cons(rose::node(UINT64_C(3),
                                              crane::list<crane::box<rose>>{}),
                                   crane::list<crane::box<rose>>{})),
            crane::list<crane::box<rose>>{}));
    static uint64_t count(const crane::list<crane::box<rose>> &l);
    static crane::list<crane::box<rose>> children(const rose &r);
  };

  template <typename F> struct Measure {
    static const uint64_t &total() {
      static const uint64_t v =
          (F::count(F::forest) + F::count(List::template flat_map<rose, rose>(
                                     F::children, F::forest)));
      return v;
    }
  };

  using M = Measure<Forest>;
  static inline const uint64_t total = M::total();
};

template <typename M>
concept FOREST = requires {
  requires(
      requires {
        {
          M::forest
        } -> std::convertible_to<
            crane::list<crane::box<BoxedElementConcept::rose>>>;
      } ||
      requires {
        {
          M::forest()
        } -> std::convertible_to<
            crane::list<crane::box<BoxedElementConcept::rose>>>;
      });
  {
    M::count(std::declval<crane::list<crane::box<BoxedElementConcept::rose>>>())
  } -> std::same_as<uint64_t>;
  {
    M::children(std::declval<BoxedElementConcept::rose>())
  } -> std::same_as<crane::list<crane::box<BoxedElementConcept::rose>>>;
};

template <typename T1>
crane::list<T1> Datatypes::app(const crane::list<T1> &l, crane::list<T1> m) {
  if (l.empty()) {
    return m;
  } else {
    const T1 &a = l.front();
    auto l1 = l.tail();
    return crane::cons(a, Datatypes::template app<T1>(l1, std::move(m)));
  }
}

template <typename T1, typename T2, typename F0>
crane::list<T2> List::flat_map(F0 &&f, const crane::list<T1> &l) {
  if (l.empty()) {
    return crane::list<T2>{};
  } else {
    const T1 &x = l.front();
    auto l0 = l.tail();
    return Datatypes::template app<T2>(f(x),
                                       List::template flat_map<T1, T2>(f, l0));
  }
}

template <typename T1, typename T2, typename F0>
T1 List::fold_left(F0 &&f, const crane::list<T2> &l, T1 a0) {
  if (l.empty()) {
    return a0;
  } else {
    const T2 &b = l.front();
    auto l0 = l.tail();
    return List::template fold_left<T1, T2>(f, l0, f(std::move(a0), b));
  }
}

#endif // INCLUDED_BOXED_ELEMENT_CONCEPT
