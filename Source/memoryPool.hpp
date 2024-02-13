#ifndef BOSSVECTORIZATIONCOORDINATORENGINE_MEMORYPOOL_H
#define BOSSVECTORIZATIONCOORDINATORENGINE_MEMORYPOOL_H

#include "config.hpp"

#include <condition_variable>
#include <functional>
#include <iostream>
#include <pthread.h>
#include <queue>

#define MEMORY_INFO

class ThreadPool {
public:
  static ThreadPool& getInstance() {
    static ThreadPool instance(vectorization::config::maxVectorizedDOP);
    return instance;
  }

  template <typename Function, typename... Args> void enqueue(Function&& f, Args&&... args) {
    {
      std::unique_lock<std::mutex> lock(queueMutex);
      tasks.emplace([=] { f(args...); });
    }
    task_cv.notify_one();
  }

  void waitUntilComplete(uint32_t tasksToComplete) {
    std::unique_lock<std::mutex> lock(tasksCountMutex);
    if(tasksCompletedCount == tasksToComplete) {
      tasksCompletedCount = 0;
      return;
    }
    wait_cv.wait(lock, [this, tasksToComplete] { return tasksCompletedCount == tasksToComplete; });
    tasksCompletedCount = 0;
  }

private:
  explicit ThreadPool(int numThreads) : stop(false), tasksCompletedCount(0) {
#ifdef MEMORY_INFO
    std::cout << "Constructing " << numThreads << " worker threads for thread pool\n";
#endif
    threads.resize(numThreads);
    for(int i = 0; i < numThreads; ++i) {
      pthread_create(&threads[i], nullptr, workerThread, reinterpret_cast<void*>(i));
    }
  }

  ~ThreadPool() {
    {
      std::unique_lock<std::mutex> lock(queueMutex);
      stop = true;
    }
    task_cv.notify_all();

    for(auto& thread : threads) {
      pthread_join(thread, nullptr);
    }
  }

  static void* workerThread(void* arg) {
    auto cpuCore = static_cast<int>(reinterpret_cast<std::intptr_t>(arg));
    cpu_set_t cpuSet;
    CPU_ZERO(&cpuSet);
    CPU_SET(cpuCore, &cpuSet);
    pthread_t thread = pthread_self();
    if(pthread_setaffinity_np(thread, sizeof(cpu_set_t), &cpuSet) != 0)
      std::cerr << "Error setting CPU affinity for thread " << cpuCore << std::endl;
#ifdef MEMORY_INFO
    std::cout << "Started worker thread running on cpu core " << cpuCore << std::endl;
#endif

    auto* pool = &getInstance();
    while(true) {
      std::function<void()> task;
      {
        std::unique_lock<std::mutex> lock(pool->queueMutex);
        pool->task_cv.wait(lock, [pool] { return pool->stop || !pool->tasks.empty(); });
        if(pool->stop && pool->tasks.empty()) {
          return nullptr;
        }
        task = std::move(pool->tasks.front());
        pool->tasks.pop();
      }
      task();
      {
        std::unique_lock<std::mutex> lock(pool->tasksCountMutex);
        ++(pool->tasksCompletedCount);
      }
      pool->wait_cv.notify_one();
    }
  }

  std::vector<pthread_t> threads;
  std::queue<std::function<void()>> tasks;
  std::mutex tasksCountMutex;
  std::mutex queueMutex;
  std::condition_variable task_cv;
  std::condition_variable wait_cv;
  bool stop;
  uint32_t tasksCompletedCount;
};

#endif // BOSSVECTORIZATIONCOORDINATORENGINE_MEMORYPOOL_H
