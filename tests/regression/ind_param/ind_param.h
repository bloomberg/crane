#ifndef INCLUDED_IND_PARAM
#define INCLUDED_IND_PARAM

#include <concepts>
#include <type_traits>
#include <utility>
#include <variant>

template <typename M>
concept Container = requires {
  typename M::elem;
  typename M::t;
  { M::size(std::declval<typename M::t>()) } -> std::same_as<uint64_t>;
};

struct IndParam {
  template <Container C> struct Wrapper {
    using wrapped = typename C::t;

    struct result {
      // TYPES
      struct Ok {
        typename C::t a0;
      };

      struct Err {
        uint64_t a0;
      };

      using variant_t = std::variant<Ok, Err>;

    private:
      // DATA
      variant_t v_;

    public:
      // CREATORS
      result() {}

      explicit result(Ok _v) : v_(std::move(_v)) {}

      explicit result(Err _v) : v_(std::move(_v)) {}

      result(const result &_other) : v_(std::move(_other.clone().v_)) {}

      result(result &&_other) noexcept : v_(std::move(_other.v_)) {}

      result &operator=(const result &_other) {
        v_ = std::move(_other.clone().v_);
        return *this;
      }

      result &operator=(result &&_other) noexcept {
        v_ = std::move(_other.v_);
        return *this;
      }

      // ACCESSORS
      result clone() const {
        if (std::holds_alternative<Ok>(this->v())) {
          const auto &[a0] = std::get<Ok>(this->v());
          return result(Ok{a0.clone()});
        } else {
          const auto &[a0] = std::get<Err>(this->v());
          return result(Err{a0});
        }
      }

      // CREATORS
      static result ok(typename C::t a0) { return result(Ok{std::move(a0)}); }

      static result err(uint64_t a0) { return result(Err{a0}); }

      // MANIPULATORS
      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }
    };

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, typename C::t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    static T1 result_rect(F0 &&f, F1 &&f0, const result &r) {
      if (std::holds_alternative<typename result::Ok>(r.v())) {
        const auto &[a0] = std::get<typename result::Ok>(r.v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename result::Err>(r.v());
        return f0(a0);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, typename C::t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    static T1 result_rec(F0 &&f, F1 &&f0, const result &r) {
      if (std::holds_alternative<typename result::Ok>(r.v())) {
        const auto &[a0] = std::get<typename result::Ok>(r.v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename result::Err>(r.v());
        return f0(a0);
      }
    }

    static result make_single(typename C::elem e) {
      return result::ok(C::t::single(e));
    }

    static result make_pair(typename C::elem e1, typename C::elem e2) {
      return result::ok(C::t::pair(e1, e2));
    }

    static uint64_t get_size(const result &r) {
      if (std::holds_alternative<typename result::Ok>(r.v())) {
        const auto &[a0] = std::get<typename result::Ok>(r.v());
        return C::size(a0);
      } else {
        return UINT64_C(0);
      }
    }

    static const result &empty_result() {
      static const result v = result::ok(C::t::empty());
      return v;
    }

    static const result &error_result() {
      static const result v = result::err(UINT64_C(404));
      return v;
    }
  };

  struct NatContainer {
    using elem = uint64_t;

    struct t {
      // TYPES
      struct Empty {};

      struct Single {
        elem a0;
      };

      struct Pair {
        elem a0;
        elem a1;
      };

      using variant_t = std::variant<Empty, Single, Pair>;

    private:
      // DATA
      variant_t v_;

    public:
      // CREATORS
      t() {}

      explicit t(Empty _v) : v_(_v) {}

      explicit t(Single _v) : v_(std::move(_v)) {}

      explicit t(Pair _v) : v_(std::move(_v)) {}

      t(const t &_other) : v_(std::move(_other.clone().v_)) {}

      t(t &&_other) noexcept : v_(std::move(_other.v_)) {}

      t &operator=(const t &_other) {
        v_ = std::move(_other.clone().v_);
        return *this;
      }

      t &operator=(t &&_other) noexcept {
        v_ = std::move(_other.v_);
        return *this;
      }

      // ACCESSORS
      t clone() const {
        if (std::holds_alternative<Empty>(this->v())) {
          return t(Empty{});
        } else if (std::holds_alternative<Single>(this->v())) {
          const auto &[a0] = std::get<Single>(this->v());
          return t(Single{a0});
        } else {
          const auto &[a0, a1] = std::get<Pair>(this->v());
          return t(Pair{a0, a1});
        }
      }

      // CREATORS
      static t empty() { return t(Empty{}); }

      static t single(elem a0) { return t(Single{std::move(a0)}); }

      static t pair(elem a0, elem a1) {
        return t(Pair{std::move(a0), std::move(a1)});
      }

      // MANIPULATORS
      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }
    };

    template <typename T1, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &, uint64_t &>
    static T1 t_rect(T1 f, F1 &&f0, F2 &&f1, const t &t0) {
      if (std::holds_alternative<typename t::Empty>(t0.v())) {
        return f;
      } else if (std::holds_alternative<typename t::Single>(t0.v())) {
        const auto &[a0] = std::get<typename t::Single>(t0.v());
        return f0(a0);
      } else {
        const auto &[a0, a1] = std::get<typename t::Pair>(t0.v());
        return f1(a0, a1);
      }
    }

    template <typename T1, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &, uint64_t &>
    static T1 t_rec(T1 f, F1 &&f0, F2 &&f1, const t &t0) {
      if (std::holds_alternative<typename t::Empty>(t0.v())) {
        return f;
      } else if (std::holds_alternative<typename t::Single>(t0.v())) {
        const auto &[a0] = std::get<typename t::Single>(t0.v());
        return f0(a0);
      } else {
        const auto &[a0, a1] = std::get<typename t::Pair>(t0.v());
        return f1(a0, a1);
      }
    }

    static uint64_t size(const t &c);
  };

  using NatWrapper = Wrapper<NatContainer>;
  static inline const NatWrapper::result test_single =
      NatWrapper::make_single(UINT64_C(42));
  static inline const NatWrapper::result test_pair =
      NatWrapper::make_pair(UINT64_C(1), UINT64_C(2));
  static inline const uint64_t test_size_single =
      NatWrapper::get_size(test_single);
  static inline const uint64_t test_size_pair = NatWrapper::get_size(test_pair);
  static inline const uint64_t test_error =
      NatWrapper::get_size(NatWrapper::error_result());
};

#endif // INCLUDED_IND_PARAM
