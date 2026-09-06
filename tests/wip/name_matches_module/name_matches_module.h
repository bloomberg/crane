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
    struct Inner {
      // DATA
      uint64_t a0;

      // ACCESSORS
      Inner clone() const { return {a0}; }

      // CREATORS
      static Inner i(uint64_t a0) { return {a0}; }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
      T1 Inner_rect(F0 &&f) const {
        const auto &[a0] = *this;
        return f(a0);
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
      T1 Inner_rec(F0 &&f) const {
        const auto &[a0] = *this;
        return f(a0);
      }

      uint64_t get() const {
        const auto &[a0] = *this;
        return a0;
      }
    };
  };

  /// A module becomes a C++ struct, so a definition or an inductive named after
  /// its enclosing module becomes a member with the same name as its class,
  /// which C++ forbids.  Both spellings are here: Inner inside module Inner,
  /// and NameMatchesModule inside module NameMatchesModule.
  static inline const uint64_t NameMatchesModule = UINT64_C(4);
  static inline const uint64_t run =
      (NameMatchesModule + Inner::i(UINT64_C(6)).get());
};

#endif // INCLUDED_NAME_MATCHES_MODULE
