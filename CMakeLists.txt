cmake_minimum_required(VERSION 3.10)
project(BOSSVectorizationCoordinatorEngine)

set(CMAKE_CXX_VISIBILITY_PRESET hidden)

if(POLICY CMP0135)
  cmake_policy(SET CMP0135 NEW)
  set(CMAKE_POLICY_DEFAULT_CMP0135 NEW)
endif()

# Configure CCache if available
find_program(CCACHE_EXECUTABLE ccache)
mark_as_advanced(CCACHE_EXECUTABLE)
if(CCACHE_EXECUTABLE)
  foreach(LANG C CXX)
    if(NOT DEFINED CMAKE_${LANG}_COMPILER_LAUNCHER AND NOT CMAKE_${LANG}_COMPILER MATCHES ".*/ccache")
      message(STATUS "Enabling ccache for ${LANG}")
      set(CMAKE_${LANG}_COMPILER_LAUNCHER ${CCACHE_EXECUTABLE} CACHE STRING "")
    endif()
  endforeach()
endif()

############################## Custom build modes ###############################

# Default flags for all build types
set(COMMON_FLAGS "-Wall -Wextra -Wpedantic -march=native")

# Debug build type
set(CMAKE_CXX_FLAGS_DEBUG "${COMMON_FLAGS} -Og -g"
        CACHE STRING
        "Flags used by the C++ compiler during Debug builds."
        FORCE)
set(CMAKE_C_FLAGS_DEBUG "${COMMON_FLAGS} -Og -g"
        CACHE STRING
        "Flags used by the C compiler during Debug builds."
        FORCE)
set(CMAKE_EXE_LINKER_FLAGS_DEBUG
        ${CMAKE_EXE_LINKER_FLAGS_DEBUG} CACHE STRING
        "Flags used for linking binaries during Debug builds."
        FORCE)
set(CMAKE_SHARED_LINKER_FLAGS_DEBUG
        ${CMAKE_SHARED_LINKER_FLAGS_DEBUG} CACHE STRING
        "Flags used by the shared libraries linker during Debug builds."
        FORCE)

# Release build type
set(CMAKE_CXX_FLAGS_RELEASE "${COMMON_FLAGS} -O3 -g0"
        CACHE STRING
        "Flags used by the C++ compiler during Release builds."
        FORCE)
set(CMAKE_C_FLAGS_RELEASE "${COMMON_FLAGS} -O3 -g0"
        CACHE STRING
        "Flags used by the C compiler during Release builds."
        FORCE)
set(CMAKE_EXE_LINKER_FLAGS_RELEASE
        ${CMAKE_EXE_LINKER_FLAGS_RELEASE} CACHE STRING
        "Flags used for linking binaries during Release builds."
        FORCE)
set(CMAKE_SHARED_LINKER_FLAGS_RELEASE
        ${CMAKE_SHARED_LINKER_FLAGS_RELEASE} CACHE STRING
        "Flags used by the shared libraries linker during Release builds."
        FORCE)

# Sanitize build type
set(CMAKE_CXX_FLAGS_SANITIZE "${COMMON_FLAGS} -fno-omit-frame-pointer -fsanitize=address,signed-integer-overflow,null,alignment,bounds,function,return,vla-bound -O0 -g"
        CACHE STRING
        "Flags used by the C++ compiler during Sanitize builds."
        FORCE)
set(CMAKE_C_FLAGS_SANITIZE "${COMMON_FLAGS} -fno-omit-frame-pointer -fsanitize=address,signed-integer-overflow,null,alignment,bounds,function,return,vla-bound -O0 -g"
        CACHE STRING
        "Flags used by the C compiler during Sanitize builds."
        FORCE)
set(CMAKE_EXE_LINKER_FLAGS_SANITIZE
        ${CMAKE_EXE_LINKER_FLAGS_DEBUG} CACHE STRING
        "Flags used for linking binaries during Sanitize builds."
        FORCE)
set(CMAKE_SHARED_LINKER_FLAGS_SANITIZE
        ${CMAKE_SHARED_LINKER_FLAGS_DEBUG} CACHE STRING
        "Flags used by the shared libraries linker during Sanitize builds."
        FORCE)
mark_as_advanced(
        CMAKE_CXX_FLAGS_DEBUG		    CMAKE_EXE_LINKER_FLAGS_DEBUG
        CMAKE_C_FLAGS_DEBUG		        CMAKE_SHARED_LINKER_FLAGS_DEBUG
        CMAKE_CXX_FLAGS_RELEASE		    CMAKE_EXE_LINKER_FLAGS_RELEASE
        CMAKE_C_FLAGS_RELEASE		    CMAKE_SHARED_LINKER_FLAGS_RELEASE
        CMAKE_CXX_FLAGS_SANITIZE		CMAKE_EXE_LINKER_FLAGS_SANITIZE
        CMAKE_C_FLAGS_SANITIZE		    CMAKE_SHARED_LINKER_FLAGS_SANITIZE
)

set(CMAKE_BUILD_TYPE "${CMAKE_BUILD_TYPE}" CACHE STRING
        "Choose the type of build, options are: None Debug Release RelWithDebInfo MinSizeRel Sanitize."
        FORCE)

############################### External Projects ###############################

set(CMAKE_POSITION_INDEPENDENT_CODE TRUE) # make sure all dependent libraries are compiled with that option

if(MSVC)
    set(BOSS_LINK_LIBRARY_PREFIX ${CMAKE_LINK_LIBRARY_PREFIX})
    set(BOSS_LINK_LIBRARY_SUFFIX ${CMAKE_LINK_LIBRARY_SUFFIX})
else()
    set(BOSS_LINK_LIBRARY_PREFIX ${CMAKE_SHARED_LIBRARY_PREFIX})
    set(BOSS_LINK_LIBRARY_SUFFIX ${CMAKE_SHARED_LIBRARY_SUFFIX})
endif(MSVC)

include(ExternalProject)

# Core BOSS
  if(NOT DEFINED BOSS_SOURCE_REPOSITORY)
    if(NOT GITHUB_TOKEN)
      message( FATAL_ERROR "You need to pass -DGITHUB_TOKEN=... to pass a github token to fetch the boss release or -DBOSS_SOURCE_REPOSITORY= for a non-github clone" )
    endif()
    set(BOSS_SOURCE_REPOSITORY https://little-big-h:${GITHUB_TOKEN}@github.com/symbol-store/BOSS.git)
  endif()
  if(NOT DEFINED BOSS_SOURCE_BRANCH)
    set(BOSS_SOURCE_BRANCH bootstrap_load_partition)
  endif()
  message("getting boss sources from ${BOSS_SOURCE_REPOSITORY}, branch ${BOSS_SOURCE_BRANCH}")
  ExternalProject_Add(BOSS
      GIT_REPOSITORY ${BOSS_SOURCE_REPOSITORY}
      GIT_TAG ${BOSS_SOURCE_BRANCH}
      GIT_SHALLOW ON
		  CMAKE_ARGS -DCMAKE_VERBOSE_MAKEFILE=${CMAKE_VERBOSE_MAKEFILE} -DCMAKE_INSTALL_PREFIX=${BOSSVectorizationCoordinatorEngine_BINARY_DIR}/deps $<IF:$<CONFIG:>,,-DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE}>
                 -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER}  -DCMAKE_C_COMPILER=${CMAKE_C_COMPILER} -DCMAKE_CXX_FLAGS=${CMAKE_CXX_FLAGS}
      BUILD_BYPRODUCTS ${BOSSVectorizationCoordinatorEngine_BINARY_DIR}/deps/lib/${BOSS_LINK_LIBRARY_PREFIX}BOSS${BOSS_LINK_LIBRARY_SUFFIX}
    )

#################################### Targets ####################################

if(MSVC)
  # not making any difference on Windows
  # and helps Visual Studio to parse it correctly as a target
  set(LibraryType SHARED)
else()
  set(LibraryType MODULE)
endif(MSVC)

if(MSVC)
  set(pluginInstallDir bin)
else()
  set(pluginInstallDir lib)
endif(MSVC)

set(ImplementationFiles
        Source/BOSSVectorizationCoordinatorEngine.cpp
        Source/config.cpp
        ../BOSSHazardAdaptiveEngine/Source/utilities/sharedDataTypes.cpp
)

add_library(BOSSVectorizationCoordinatorEngine MODULE ${ImplementationFiles})
set_property(TARGET BOSSVectorizationCoordinatorEngine PROPERTY CXX_STANDARD 20) ## the core is c++ 17 but the engines may want to use 20
target_include_directories(BOSSVectorizationCoordinatorEngine SYSTEM PUBLIC ${BOSSVectorizationCoordinatorEngine_BINARY_DIR}/deps/include)
target_link_directories(BOSSVectorizationCoordinatorEngine PUBLIC ${BOSSVectorizationCoordinatorEngine_BINARY_DIR}/deps/lib)
add_dependencies(BOSSVectorizationCoordinatorEngine BOSS)

find_library(NUMA_LIBRARY numa)
target_link_libraries(BOSSVectorizationCoordinatorEngine ${NUMA_LIBRARY})

set_target_properties(BOSSVectorizationCoordinatorEngine PROPERTIES INSTALL_RPATH_USE_LINK_PATH TRUE)
install(TARGETS BOSSVectorizationCoordinatorEngine LIBRARY DESTINATION lib)

set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)
