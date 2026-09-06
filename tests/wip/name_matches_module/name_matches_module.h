#ifndef INCLUDED_NAME_MATCHES_MODULE
#define INCLUDED_NAME_MATCHES_MODULE

#include <type_traits>
#include <variant>

/// A module becomes a C++ struct, so a definition or an inductive named after
/// its enclosing module becomes a member with the same name as its class,
/// which C++ forbids.  Both spellings are here: Inner inside module Inner,
/// and NameMatchesModule inside module NameMatchesModule.
struct NameMatchesModule {
  struct Inner {
    struct Inner0 {
      // DATA
      uint64_t a0;

      // ACCESSORS
      Inner0 clone() const { return {a0}; }

      // CREATORS
      static Inner0 i(uint64_t a0) { return {a0}; }
    };

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
    static T1 Inner_rect(F0 &&f, const Inner0 &i) {
      const auto &[a0] = i;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
    static T1 Inner_rec(F0 &&f, const Inner0 &i) {
      const auto &[a0] = i;
      return f(a0);
    }

    static uint64_t get(const Inner0 &x);
  };

  /// A module becomes a C++ struct, so a definition or an inductive named after
  /// its enclosing module becomes a member with the same name as its class,
  /// which C++ forbids.  Both spellings are here: Inner inside module Inner,
  /// and NameMatchesModule inside module NameMatchesModule.
  static inline const uint64_t NameMatchesModule0 = UINT64_C(4);
  static inline const uint64_t run =
      (NameMatchesModule0 + Inner::get(Inner::Inner0::i(UINT64_C(6))));
};

#endif // INCLUDED_NAME_MATCHES_MODULE
