#include <nonatomic_rc_thread_race.h>

int main() {
  // Any one round races; repeating makes the corruption reliable rather than
  // occasional.
  for (int i = 0; i < 20; ++i) {
    NonatomicRcThreadRace::run();
  }
  return 0;
}
