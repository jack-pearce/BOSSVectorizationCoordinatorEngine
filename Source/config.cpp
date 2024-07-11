#include "config.hpp"

namespace vectorization::config {

int maxVectorizedDOP = 1;
int minBuildSideTableLengthForPartitionedHashJoin = 5'000'000;

} // namespace vectorization::config
