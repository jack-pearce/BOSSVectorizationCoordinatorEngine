#ifndef BOSSVECTORIZATIONCOORDINATORENGINE_MEMORYPOOL_H
#define BOSSVECTORIZATIONCOORDINATORENGINE_MEMORYPOOL_H

#include "config.hpp"
#include <condition_variable>
#include <functional>
#include <iostream>
#include <numa.h>
#include <pthread.h>
#include <queue>

// #define MEMORY_INFO

class ThreadPool {
public:
  static ThreadPool& getInstance() {
    static ThreadPool instance(vectorization::config::maxVectorizedDOP);
    return instance;
  }

  template <typename Function, typename... Args> void enqueue(Function&& f, Args&&... args) {
    std::lock_guard<std::mutex> lock(mutex);
    tasks.emplace([func = std::forward<Function>(f),
                   arguments = std::make_tuple(std::forward<Args>(args)...)]() mutable {
      std::apply(std::move(func), std::move(arguments));
    });
    cv.notify_one();
  }

private:
  explicit ThreadPool(size_t numThreads) : stop(false), numaMachine(false) {
    if(numa_available() == 0 && numa_max_node() > 0) {
      numaMachine = true;
#ifdef MEMORY_INFO
      std::cout << "Running on NUMA machine\n";
#endif
    }
#ifdef MEMORY_INFO
    std::cout << "Constructing " << numThreads << " worker threads for thread pool\n";
#endif
    threads.resize(numThreads);
    for(size_t i = 0; i < numThreads; ++i) {
      pthread_create(&threads[i], nullptr, workerThread, reinterpret_cast<void*>(i));
    }
  }

  ~ThreadPool() {
    stop = true;
    cv.notify_all();
    for(auto& thread : threads) {
      pthread_join(thread, nullptr);
    }
  }

  static void* workerThread(void* arg) {
    auto& pool = getInstance();

    auto cpuCore = static_cast<int>(reinterpret_cast<std::intptr_t>(arg));
    cpu_set_t cpuSet;
    CPU_ZERO(&cpuSet);
    CPU_SET(cpuCore, &cpuSet);
    pthread_t thread = pthread_self();
    if(pthread_setaffinity_np(thread, sizeof(cpu_set_t), &cpuSet) != 0)
      std::cerr << "Error setting CPU affinity for thread " << cpuCore << std::endl;
#ifdef MEMORY_INFO
    std::cout << "Started worker thread running on cpu core " << cpuCore << "\n";
#endif

    if(pool.numaMachine) {
      int numaNode = numa_node_of_cpu(cpuCore);
      if(numa_run_on_node(numaNode) < 0) {
        std::cerr << "Error setting affinity of thread " << cpuCore << " to NUMA node " << numaNode
                  << std::endl;
      }
#ifdef MEMORY_INFO
      std::cout << "Pinned thread " << cpuCore << " to numa node " << numaNode << "\n";
#endif
    }

    std::function<void()> task;
    while(true) {
      {
        std::unique_lock<std::mutex> lock(pool.mutex);
        pool.cv.wait(lock, [&pool] { return pool.stop || !pool.tasks.empty(); });
        if(pool.stop && pool.tasks.empty()) {
          return nullptr;
        }
        task = std::move(pool.tasks.front());
        pool.tasks.pop();
      }

      task();
    }
  }

  std::vector<pthread_t> threads;
  std::queue<std::function<void()>> tasks;
  std::mutex mutex;
  std::condition_variable cv;
  bool stop;
  bool numaMachine;
};

class Synchroniser {
public:
  static Synchroniser& getInstance() {
    static Synchroniser instance;
    return instance;
  }

  void taskComplete() {
    std::lock_guard<std::mutex> lock(mutex);
    tasksCompletedCount++;
    cv.notify_one();
  }

  void waitUntilComplete(int tasksToComplete) {
    std::unique_lock<std::mutex> lock(mutex);
    cv.wait(lock, [this, tasksToComplete] { return tasksCompletedCount == tasksToComplete; });
    tasksCompletedCount = 0;
  }

private:
  Synchroniser() : tasksCompletedCount(0) {
#ifdef MEMORY_INFO
    std::cout << "Constructing thread synchroniser object\n";
#endif
  }

  std::mutex mutex;
  std::condition_variable cv;
  int tasksCompletedCount;
};

#endif // BOSSVECTORIZATIONCOORDINATORENGINE_MEMORYPOOL_H
