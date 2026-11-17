#pragma once

template <typename M>
concept MinSIG = requires {
  typename M::template otherE<void>;
};

struct RocqBug14100 {
  enum class NondetE { OR };

  struct Min {
    template <typename x = void> using otherE = NondetE;
  };

  static_assert(MinSIG<Min>);
};
