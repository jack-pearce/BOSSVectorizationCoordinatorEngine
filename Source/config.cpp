#include "config.hpp"

namespace vectorization::config {

int maxVectorizedDOP = 1;
int minBuildSideTableLengthForPartitionedHashJoin = 5'000'000;

int nonAdaptiveEngineIndex = 0;    // Excluding storage engine
int hazardAdaptiveEngineIndex = 1; // Excluding storage engine
int veloxEngineIndex = 2;          // Excluding storage engine

} // namespace vectorization::config
