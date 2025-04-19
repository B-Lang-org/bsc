/* Implementations of $random and $random_range */
#include <cstdlib>
#include "bluesim_kernel_api.h"
#include <map>

static std::map<tSimStateHdl, tUInt32> rand_seed_map;

// Function to generate a random number
// This function uses the provided seed to initialize the random number generator
tUInt32 local_dollar_random(tSimStateHdl simHdl, tUInt32 seed) {
  srand(seed);
  tUInt32 result = random();
  rand_seed_map[simHdl] = result;
  return result;
}

// Overload for (simHdl, const char*, rand_seed)
// Uses the provided seed
tUInt32 dollar_random(tSimStateHdl simHdl, const char*, tUInt32 rand_seed) {
  return local_dollar_random(simHdl, rand_seed);
}

// Overload for (simHdl, const char*)
// Uses the existing seed from rand_seed_map or initializes it to 1
// if this is the first call for this simHdl
tUInt32 dollar_random(tSimStateHdl simHdl) {
  tUInt32 seed = 1;
  auto it = rand_seed_map.find(simHdl);
  if (it == rand_seed_map.end()) {
      // First call: use seed 1
      rand_seed_map[simHdl] = seed;
  } else {
      // Use the existing seed
      seed = it->second;
  }

  return local_dollar_random(simHdl,seed);
}

// Uniform random in range [minval, maxval]
tUInt32 dollar_urandom_range(tSimStateHdl simHdl,
                             const char*,
                             tUInt32 maxval,
                             tUInt32 minval = 0) {
    if (maxval < minval) return minval;
    tUInt32 range = maxval - minval + 1;
    tUInt32 seed = 1;
    auto it = rand_seed_map.find(simHdl);
    if (it == rand_seed_map.end()) {
        // First call: use seed 1
        rand_seed_map[simHdl] = seed;
    } else {
        // Use the existing seed
        seed = it->second;
    }
    return (local_dollar_random(simHdl, seed) % range) + minval;
}
