
#include <stdlib.h>
#include <assert.h>
#include <string.h>



#define QUEUE_EMPTY NULL
#define QUEUE_ABORT NULL
static struct subtask* const STEAL_RES_EMPTY = (struct subtask*) 0;
static struct subtask* const STEAL_RES_ABORT = (struct subtask*) 1;

static const int mem_model = __ATOMIC_SEQ_CST;
static const int strong = 0;
static const int backoff_nb_cycles = 1l << 10;



static inline
uint64_t rdtsc() {
  unsigned int hi, lo;
  __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
  return  ((uint64_t) lo) | (((uint64_t) hi) << 32);
}

static inline
void rdtsc_wait(uint64_t n) {
  const uint64_t start = rdtsc();
  while (rdtsc() < (start + n)) {
    __asm__("PAUSE");
  }
}
static inline
void spin_for(uint64_t nb_cycles) {
  rdtsc_wait(nb_cycles);
}

static inline struct subtask* cb_get(struct subtask **buf, int64_t capacity, int64_t i)  {
  return (struct subtask*)__atomic_load_n(&buf[i % capacity], __ATOMIC_RELAXED);
}

static inline void cb_put (struct subtask **buf, int64_t capacity, int64_t i, struct subtask* x) {
  __atomic_store_n(&buf[i % capacity], x, __ATOMIC_RELAXED);
}

static inline int stealable(struct subtask **buf, int64_t capacity, int64_t i) {
  return __atomic_load_n(&buf[i % capacity]->been_stolen, __ATOMIC_RELAXED);
}


struct subtask ** grow(struct subtask **old_buf,
                       int64_t old_capacity,
                       int64_t new_capacity,
                       int64_t b,
                       int64_t t) {
  struct subtask ** new_buf = calloc(new_capacity, sizeof(struct subtask*));
  for (int64_t i = t; i < b; i++) {
    cb_put(new_buf, new_capacity, i, cb_get(old_buf, old_capacity, i));
  }
  return new_buf;
}

static inline int deque_init(struct deque *q, int64_t capacity) {
  assert(q != NULL);
  memset(q, 0, sizeof(struct deque));

  q->size = capacity;
  q->buffer = calloc(capacity, sizeof(struct subtask*));

  if (q->buffer == NULL) {
    return -1;
  }
  return 0;
}

static inline int cas_top (struct deque *q, int64_t old_val, int64_t new_val) {
  int64_t ov = old_val;
  if(__atomic_compare_exchange_n(&q->top, &ov, new_val, strong, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED)) {
    return 1;
  }
  spin_for(backoff_nb_cycles);
  return false;
}


static inline void push_back(struct deque *q, struct subtask*subtask)
{
  assert(subtask != NULL);
  assert(q != NULL);

  int64_t b = __atomic_load_n(&q->bottom, __ATOMIC_RELAXED); // load atomically
  int64_t t = __atomic_load_n(&q->top, __ATOMIC_ACQUIRE);    // load atomically
  if (b-t >= (__atomic_load_n(&q->size, __ATOMIC_RELAXED) - 1)) {
    // grow_queue
    struct subtask **old_buf = q->buffer;
    int64_t old_capacity = __atomic_load_n(&q->size, __ATOMIC_RELAXED);
    int64_t new_capacity = __atomic_load_n(&q->size, __ATOMIC_RELAXED) * 2;
    __atomic_store_n(&q->buffer, grow(old_buf, old_capacity, new_capacity, b, t), __ATOMIC_RELAXED);
    __atomic_store_n(&q->size, new_capacity, __ATOMIC_RELAXED);
  }
  cb_put(q->buffer, q->size , b, subtask);
  __atomic_thread_fence(__ATOMIC_RELEASE);
  __atomic_store_n(&q->bottom, b+1, __ATOMIC_RELAXED);
  return;
}


static inline struct subtask * pop_back(struct deque *q)
{
  int64_t b = __atomic_load_n(&q->bottom, __ATOMIC_RELAXED) - 1; // load atomically
  __atomic_store_n(&q->bottom, b, __ATOMIC_RELAXED);
	__atomic_thread_fence(__ATOMIC_SEQ_CST);

  int64_t t = __atomic_load_n(&q->top, __ATOMIC_RELAXED);
  if (b < t) {
    __atomic_store_n(&q->bottom, t, __ATOMIC_RELAXED);
    return NULL;
  }
  struct subtask* item = cb_get(q->buffer, __atomic_load_n(&q->size, __ATOMIC_RELAXED), b);
  if (b > t) {
    return item;
  }

  if (!cas_top(q, t, t + 1)) {
    item = NULL;
  }
  __atomic_store_n(&q->bottom, t+1, __ATOMIC_RELAXED);
  return item;
}

static inline struct subtask* steal(struct deque *q)
{
  assert(q != NULL);

  int64_t t = __atomic_load_n(&q->top, __ATOMIC_ACQUIRE);    // load atomically
  __atomic_thread_fence(__ATOMIC_SEQ_CST);
  int64_t b = __atomic_load_n(&q->bottom, __ATOMIC_ACQUIRE); // load atomically

  if (t >= b) {
    return STEAL_RES_EMPTY;
  }
  struct subtask* item = cb_get(q->buffer, __atomic_load_n(&q->size, __ATOMIC_RELAXED), t);

  if (!cas_top(q, t, t + 1)) {
    return STEAL_RES_ABORT;
  }

  return item;
}



static inline size_t nb_threads(struct deque *q) {
  return (size_t)__atomic_load_n(&q->bottom, __ATOMIC_RELAXED) - __atomic_load_n(&q->top, __ATOMIC_RELAXED);
}

static inline int empty(struct deque *q) {
  return nb_threads(q) < 1;
}

static inline struct subtask* setup_subtask(sub_task_fn fn,
                                            void* args,
                                            const char* name,
                                            pthread_mutex_t *mutex,
                                            pthread_cond_t *cond,
                                            volatile int* counter,
                                            int start, int end,
                                            int chunk, int id)
{
  struct subtask* subtask = malloc(sizeof(struct subtask));
  if (subtask == NULL) {
    assert(!"malloc failed in setup_subtask");
    return  NULL;
  }
  subtask->fn      = fn;
  subtask->args    = args;
  subtask->name    = name;
  subtask->mutex   = mutex;
  subtask->cond    = cond;
  subtask->counter = counter;
  subtask->start   = start;
  subtask->end     = end;
  subtask->chunkable   = chunk;
  // This should start at the value of minimum work pr. subtask
  subtask->iterations = chunk;
  subtask->id      = id;
  subtask->been_stolen = 0;
  return subtask;
}