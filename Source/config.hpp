#ifndef BOSSVECTORIZATIONCOORDINATORENGINE_CONFIG_HPP
#define BOSSVECTORIZATIONCOORDINATORENGINE_CONFIG_HPP

namespace vectorization::config {

extern int maxVectorizedDOP;
extern int minBuildSideTableLengthForPartitionedHashJoin;

extern int nonAdaptiveEngineIndex;
extern int hazardAdaptiveEngineIndex;
extern int veloxEngineIndex;

} // namespace vectorization::config

#endif // BOSSVECTORIZATIONCOORDINATORENGINE_CONFIG_HPP
