#pragma once

enum class Bool0;
enum class Bool0 { TRUE_, FALSE_ };

struct RocqBug3287 {
  struct Foo {
    static constexpr Bool0 bar = Bool0::TRUE_;
  };

  struct Foo_ {
    static constexpr Bool0 bar = Bool0::TRUE_;
  };

  static inline const Bool0 bar1 = Foo::bar;
  static inline const Bool0 bar2 = Foo_::bar;
};
