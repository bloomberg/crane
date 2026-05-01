#include <loopify_mutual_countdown.h>

bool LoopifyMutualCountdown::even_countdown(const unsigned int n) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n_ = n - 1;
    return odd_countdown(n_);
  }
}

bool LoopifyMutualCountdown::odd_countdown(const unsigned int n) {
  if (n <= 0) {
    return false;
  } else {
    unsigned int n_ = n - 1;
    return even_countdown(n_);
  }
}
