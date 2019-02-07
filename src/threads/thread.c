#include "threads/thread.h"
#include <debug.h>
#include <stddef.h>
#include <random.h>
#include <stdio.h>
#include <string.h>
#include "fixed-point.h"
#include "devices/timer.h"
#include "threads/flags.h"
#include "threads/interrupt.h"
#include "threads/intr-stubs.h"
#include "threads/palloc.h"
#include "threads/switch.h"
#include "threads/synch.h"
#include "threads/vaddr.h"

#ifdef USERPROG
#include "userprog/process.h"
#endif

/* Random value for struct thread's `magic' member.
   Used to detect stack overflow.  See the big comment at the top
   of thread.h for details. */
#define THREAD_MAGIC 0xcd6abf4b

/* List of processes in THREAD_READY state, that is, processes
   that are ready to run but not actually running. */
static struct list ready_list;

/* List of all processes.  Processes are added to this list
   when they are first scheduled and removed when they exit. */
static struct list all_list;

static struct list sleeping_threads;
static int64_t next_wakeup_time;

/* Idle thread. */
static struct thread *idle_thread;

/* wakeup thread */
static struct thread *wakeup_thread;

/* scheduler thread */
static struct thread *scheduler_thread;

/* Initial thread, the thread running init.c:main(). */
static struct thread *initial_thread;

/* Lock used by allocate_tid(). */
static struct lock tid_lock;

/* Lock used by timer_wakeup() and thread_block_till(). */
static struct lock sleepers_lock;

/* Stack frame for kernel_thread(). */
struct kernel_thread_frame 
  {
    void *eip;                  /* Return address. */
    thread_func *function;      /* Function to call. */
    void *aux;                  /* Auxiliary data for function. */
  };

/* Statistics. */
static long long idle_ticks;    /* # of timer ticks spent idle. */
static long long kernel_ticks;  /* # of timer ticks in kernel threads. */
static long long user_ticks;    /* # of timer ticks in user programs. */
static int load_avg;

/* Scheduling. */
#define TIME_SLICE 4            /* # of timer ticks to give each thread. */
static unsigned thread_ticks;   /* # of timer ticks since last yield. */

/* If false (default), use round-robin scheduler.
   If true, use multi-level feedback queue scheduler.
   Controlled by kernel command-line option "-o mlfqs". */
bool thread_mlfqs;

static void kernel_thread (thread_func *, void *aux);

static void idle (void *aux UNUSED);
static void wakeup_manager (void *aux UNUSED);
static void scheduler_manager (void *aux UNUSED);
static struct thread *running_thread (void);
static struct thread *next_thread_to_run (void);
static void init_thread (struct thread *, const char *name, int priority);
static bool is_thread (struct thread *);
static void *alloc_frame (struct thread *, size_t size);
static void schedule (void);
void schedule_tail (struct thread *prev);
static tid_t allocate_tid (void);

struct thread* tid_mapping[2041];
int tid_load_complete[2041];
int tid_return_val[2041];
struct file* file_ptr[2041];
int file_counter[2041];
int counter;

bool priority_encoder(const struct list_elem *A, const struct list_elem *B, void *aux UNUSED){
	// return effective_priority(list_entry(A, struct thread, elem)) > effective_priority(list_entry(B, struct thread, elem));
  return list_entry(A, struct thread, elem)->priority < list_entry(B, struct thread, elem)->priority;
}

bool sleeping_encoder(const struct list_elem *A, const struct list_elem *B, void *aux UNUSED){
	return list_entry(A, struct thread, elem)->wakeup_time < list_entry(B, struct thread, elem)->wakeup_time;
}

static int64_t min(int64_t A, int64_t B){
	if(A<B){
		return A;
	}
	return B;
}

static int min_int(int A, int B){
	if(A<B){
		return A;
	}
	return B;
}

static int max(int A, int B){
  if(A<B){
    return B;
  }
  return A;
}

/* Initializes the threading system by transforming the code
   that's currently running into a thread.  This can't work in
   general and it is possible in this case only because loader.S
   was careful to put the bottom of the stack at a page boundary.

   Also initializes the run queue and the tid lock.

   After calling this function, be sure to initialize the page
   allocator before trying to create any threads with
   thread_create().

   It is not safe to call thread_current() until this function
   finishes. */
void
thread_init (void) 
{
  ASSERT (intr_get_level () == INTR_OFF);
  lock_init (&sleepers_lock);
  lock_init (&tid_lock);
  list_init (&ready_list);
  list_init (&all_list);
  list_init (&sleeping_threads);
  next_wakeup_time = INT64_MAX;
  load_avg = 0;
  /* Set up a thread structure for the running thread. */
  initial_thread = running_thread ();
  init_thread (initial_thread, "main", PRI_DEFAULT);
  initial_thread->status = THREAD_RUNNING;
  initial_thread->tid = allocate_tid ();

  counter=0;
  memset(tid_mapping,NULL,sizeof(tid_mapping));
  memset(file_ptr,NULL,sizeof(file_ptr));
  memset(tid_load_complete,0,sizeof(tid_load_complete));
  memset(file_counter, 0, sizeof(file_counter));
  memset(tid_return_val,-2,sizeof(tid_return_val));
  tid_mapping[initial_thread->tid] = thread_current();
}

/* Starts preemptive thread scheduling by enabling interrupts.
   Also creates the idle thread. */
void
thread_start (void) 
{
  /* Create the idle thread. */
  struct semaphore idle_started;
  sema_init (&idle_started, 0);
  thread_create ("idle", PRI_MIN, idle, &idle_started);
  load_avg = 0;
  /* Start preemptive thread scheduling. */
  intr_enable ();

  /* Wait for the idle thread to initialize idle_thread. */
  sema_down (&idle_started);
  thread_create ("manager_th", PRI_MAX, wakeup_manager, NULL);
  thread_create ("scheduler", PRI_MAX, scheduler_manager, NULL);
}

/* Called by the timer interrupt handler at each timer tick.
   Thus, this function runs in an external interrupt context. */
void
thread_tick (void) 
{
  struct thread *t = thread_current ();
  if(t != idle_thread && t!= scheduler_thread && t!= wakeup_thread){
    t->recent_cpu = add_float_int(t->recent_cpu, 1);
  }
  /* Update statistics. */
  if (t == idle_thread)
    idle_ticks++;
#ifdef USERPROG
  else if (t->pagedir != NULL)
    user_ticks++;
#endif
  else
    kernel_ticks++;
  
// to wake up the manager thread if a thread needs to be woken up.
  if(next_wakeup_time <= timer_ticks() && wakeup_thread->status == THREAD_BLOCKED){
    // thread_set_next_wakeup();
    thread_unblock(wakeup_thread);
  }
  // thread_wakeup(list_begin(&sleeping_threads), timer_ticks());

  /* Enforce preemption. */
  if (++thread_ticks >= TIME_SLICE){
    intr_yield_on_return ();
  }

// to avoid starvation  , decrease the priority by 1.
  if(thread_mlfqs && timer_ticks()>0){
    if(thread_ticks>=TIME_SLICE){
      t->priority = max(PRI_MIN, t->priority-1);
      // thread_update_priority(t);
    }
    if(timer_ticks()%TIMER_FREQ == 0 && scheduler_thread!=NULL && scheduler_thread->status == THREAD_BLOCKED){
      thread_unblock(scheduler_thread);
    }
  }

}

/* Prints thread statistics. */
void
thread_print_stats (void) 
{
  printf ("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n",
          idle_ticks, kernel_ticks, user_ticks);
}


/* Creates a new kernel thread named NAME with the given initial
   PRIORITY, which executes FUNCTION passing AUX as the argument,
   and adds it to the ready queue.  Returns the thread identifier
   for the new thread, or TID_ERROR if creation fails.

   If thread_start() has been called, then the new thread may be
   scheduled before thread_create() returns.  It could even exit
   before thread_create() returns.  Contrariwise, the original
   thread may run for any amount of time before the new thread is
   scheduled.  Use a semaphore or some other form of
   synchronization if you need to ensure ordering.

   The code provided sets the new thread's `priority' member to
   PRIORITY, but no actual priority scheduling is implemented.
   Priority scheduling is the goal of Problem 1-3. */
tid_t
thread_create (const char *name, int priority,
               thread_func *function, void *aux) 
{
  struct thread *t;
  struct kernel_thread_frame *kf;
  struct switch_entry_frame *ef;
  struct switch_threads_frame *sf;
  tid_t tid;
  enum intr_level old_level;

  ASSERT (function != NULL);


  /* Allocate thread. */
  t = palloc_get_page (PAL_ZERO);
  if (t == NULL)
    return TID_ERROR;

  /* Initialize thread. */
  init_thread (t, name, priority);
  tid = t->tid = allocate_tid ();

  tid_mapping[tid] = t;
  /* Prepare thread for first run by initializing its stack.
     Do this atomically so intermediate values for the 'stack' 
     member cannot be observed. */
  old_level = intr_disable ();

  /* Stack frame for kernel_thread(). */
  kf = alloc_frame (t, sizeof *kf);
  kf->eip = NULL;
  kf->function = function;
  kf->aux = aux;

  /* Stack frame for switch_entry(). */
  ef = alloc_frame (t, sizeof *ef);
  ef->eip = (void (*) (void)) kernel_thread;

  /* Stack frame for switch_threads(). */
  sf = alloc_frame (t, sizeof *sf);
  sf->eip = switch_entry;
  sf->ebp = 0;
  intr_set_level (old_level);

  /* Add to run queue. */
  thread_unblock (t);
  /* if the new thread has higher priority than running thread, yield the processor to it. */
  // if(thread_current()->priority < t->priority){
  //   thread_yield();
  // }
  struct list_elem *current_top_ready = list_max(&ready_list, priority_encoder, NULL);
  struct thread *ready_threads_head;
  ready_threads_head = list_entry(current_top_ready, struct thread, elem);
  if(ready_threads_head->priority > thread_current()->priority){
    if (intr_context ()){
      intr_yield_on_return ();
    }
    else{
      thread_yield ();
    }
  }
  // thread_yield();
  return tid;
}

/* Puts the current thread to sleep.  It will not be scheduled
   again until awoken by thread_unblock().

   This function must be called with interrupts turned off.  It
   is usually a better idea to use one of the synchronization
   primitives in synch.h. */
void
thread_block (void) 
{
  ASSERT (!intr_context ());
  ASSERT (intr_get_level () == INTR_OFF);

  thread_current ()->status = THREAD_BLOCKED;
  schedule ();
}

/* Transitions a blocked thread T to the ready-to-run state.
   This is an error if T is not blocked.  (Use thread_yield() to
   make the running thread ready.)

   This function does not preempt the running thread.  This can
   be important: if the caller had disabled interrupts itself,
   it may expect that it can atomically unblock a thread and
   update other data. */
void
thread_unblock (struct thread *t) 
{
  enum intr_level old_level;

  ASSERT (is_thread (t));

  old_level = intr_disable ();
  ASSERT (t->status == THREAD_BLOCKED);
  // list_insert_ordered (&ready_list, &t->elem, priority_encoder, NULL);
  list_push_back (&ready_list, &t->elem);
  t->status = THREAD_READY;
  intr_set_level (old_level);
}

/* Returns the name of the running thread. */
const char *
thread_name (void) 
{
  return thread_current ()->name;
}

/* Returns the running thread.
   This is running_thread() plus a couple of sanity checks.
   See the big comment at the top of thread.h for details. */
struct thread *
thread_current (void) 
{
  struct thread *t = running_thread ();
  
  /* Make sure T is really a thread.
     If either of these assertions fire, then your thread may
     have overflowed its stack.  Each thread has less than 4 kB
     of stack, so a few big automatic arrays or moderate
     recursion can cause stack overflow. */
  ASSERT (is_thread (t));
  ASSERT (t->status == THREAD_RUNNING);

  return t;
}

/* Returns the running thread's tid. */
tid_t
thread_tid (void) 
{
  return thread_current ()->tid;
}

/* Deschedules the current thread and destroys it.  Never
   returns to the caller. */
void
thread_exit (void) 
{
  ASSERT (!intr_context ());

#ifdef USERPROG
  process_exit ();
#endif

  /* Remove thread from all threads list, set our status to dying,
     and schedule another process.  That process will destroy us
     when it call schedule_tail(). */
  intr_disable ();
  list_remove (&thread_current()->allelem);
  thread_current ()->status = THREAD_DYING;
  schedule ();
  NOT_REACHED ();
}

/* Yields the CPU.  The current thread is not put to sleep and
   may be scheduled again immediately at the scheduler's whim. */
void
thread_yield (void) 
{
  struct thread *cur = thread_current ();
  enum intr_level old_level;
  
  ASSERT (!intr_context ());

  old_level = intr_disable ();
  if (cur != idle_thread) {
    // list_insert_ordered (&ready_list, &cur->elem, priority_encoder, NULL);
    list_push_back (&ready_list, &cur->elem);
  }
  cur->status = THREAD_READY;
  schedule ();
  intr_set_level (old_level);
}

/* Invoke function 'func' on all threads, passing along 'aux'.
   This function must be called with interrupts off. */
void
thread_foreach (thread_action_func *func, void *aux)
{
  struct list_elem *e;

  ASSERT (intr_get_level () == INTR_OFF);

  for (e = list_begin (&all_list); e != list_end (&all_list);
       e = list_next (e))
    {
      struct thread *t = list_entry (e, struct thread, allelem);
      func (t, aux);
    }
}

/* Sets the current thread's priority to NEW_PRIORITY. */
void thread_set_priority (int new_priority) 
{
  struct thread* curr_thread = thread_current();
  /* storing the old priority in actual_priority of thread */
  int old_priority = curr_thread->priority;
  curr_thread->actual_priority = old_priority;

  /* this condition is only true when it has not got any donated priority
     it is specially helpful so that the value of priority_before_donation
     is not affected due to various priorities being donated to it */
  if(curr_thread->priority == curr_thread->priority_before_donation){
    curr_thread->priority = new_priority;
  }
  if(thread_mlfqs){
    curr_thread->priority = new_priority;
  }
  
  /* storing the actual priority in this variable */
  curr_thread->priority_before_donation = new_priority;
  /* we shall compaer the priority of the running thread with the one
     having maximum priority and if its less, preempt the processor */
  if(list_empty(&ready_list)){
		return;
  }
  struct list_elem *current_top_ready = list_max(&ready_list, priority_encoder, NULL);
  // struct list_elem *current_top_ready = list_begin(&ready_list);
  struct thread *ready_threads_head;
  ready_threads_head = list_entry(current_top_ready, struct thread, elem);
  if(ready_threads_head->priority > new_priority){
    if (intr_context ()){
      intr_yield_on_return ();
    }
    else{
      thread_yield ();
    }
  }
}

/* Returns the current thread's priority. */
int thread_get_priority () 
{
  return thread_current ()->priority;
}

/* wont be used but kept for debugging purpose if any */
int effective_priority(struct thread* root){
  if(list_empty(&root->lock_acquired)){
    return root->priority;
  }
  else{
    int max_priority = root->priority;
    struct list_elem* list_pointer = list_begin(&root->lock_acquired);
    struct list_elem* list_ending = list_end(&root->lock_acquired);
    while(list_pointer != list_ending){
      struct lock* next_lock = list_entry(list_pointer, struct lock, elem);
      if(list_empty(&next_lock->semaphore.waiters)){
        list_pointer = list_next(list_pointer);
        continue;
      }
      struct list_elem *lock_pointer, *lock_end;
      lock_pointer = list_begin(&next_lock->semaphore.waiters);
      lock_end = list_end(&next_lock->semaphore.waiters);
      while(lock_pointer != lock_end){
        struct thread *th = list_entry(lock_pointer, struct thread, elem);
        max_priority = max(max_priority, effective_priority(th));
        lock_pointer = list_next(lock_pointer);
      }
      list_pointer = list_next(list_pointer);
    }
    return max_priority;
  }
}

/* To update the priority of a thread.*/
void thread_update_priority(struct thread* up_thread){
  if (up_thread == idle_thread || up_thread == wakeup_thread || up_thread == scheduler_thread) {
    return;
  }
  int reduction = add_float_float(div_float_int(up_thread->recent_cpu, 4), mul_float_int(int_to_fixedpt(up_thread->nice_value),2));
  // int new_priority = convert_x_to_integer_zero(substract_y_from_x(convert_n_to_fixed_point(PRI_MAX), reduction));
  int new_priority = PRI_MAX - fixedpt_to_int(reduction);
  up_thread->priority = min_int(PRI_MAX, max(PRI_MIN, new_priority));
}

void update_load_avg(void){
  int ready_threads ;
  if(!list_empty(&ready_list)){
    ready_threads = list_size (&ready_list); // to calculate the number of processes in ready list. 
  }
  else{
    ready_threads = 0;
  }
  if(wakeup_thread && wakeup_thread->status == THREAD_READY)  {
    ready_threads--;
  }
  if(scheduler_thread && scheduler_thread->status == THREAD_READY) {
    ready_threads--;
  }
  if (thread_current() != idle_thread && thread_current() != scheduler_thread && thread_current() != wakeup_thread) ready_threads++;

  ASSERT(ready_threads >= 0)

  int term1 = div_float_float (59, 60);  /*term1 is fixed-point here*/
  term1 = mul_float_float (term1, load_avg);  /*term1 is fixed-point, both inputs are fixed-point*/
  int term2 = div_float_float (ready_threads, 60);   /*Both inputs are normal integer so no conversion required, term2 is fixed-point*/
  term1 = add_float_float (term1, term2);     /*everything is fixed-point*/
  
  load_avg = term1;     /*load_avg is fixed-point*/
}

/*This function updates the recent cpu of a thread. */
void update_recent_cpu(struct thread* curr_thread){
  if (curr_thread == idle_thread || curr_thread == wakeup_thread || curr_thread == scheduler_thread) {
    return;
  }
  int term1 = mul_float_int (load_avg, 2);  /*load_avg and term1 in fixed-point*/
  int term2 = add_float_int(term1 , 1); /* term2 is fixed-point */
  term1 = mul_float_float (term1, curr_thread->recent_cpu); /* everything fixed-point*/
  term1 = div_float_float (term1, term2); /*everything fixed-point*/
  term1 = add_float_int (term1, curr_thread->nice_value); /*second value integer and term1 fixed-point before and after*/
  
  curr_thread->recent_cpu = term1;
}

/* Sets the current thread's nice value to NICE. */
void
thread_set_nice (int nice UNUSED) 
{
  struct thread* curr_thread = thread_current();
  curr_thread->nice_value = nice;
  thread_update_priority(curr_thread);

  if(list_empty(&ready_list)){
		return;
  }
  struct list_elem *current_top_ready = list_max(&ready_list, priority_encoder, NULL);
  struct thread *ready_threads_head;
  ready_threads_head = list_entry(current_top_ready, struct thread, elem);
  if(ready_threads_head->priority > curr_thread->priority){
    if (intr_context ()){
      intr_yield_on_return ();
    }
    else{
      thread_yield ();
    }
  }
}

/* Returns the current thread's nice value. */
int
thread_get_nice (void) 
{
  // return 0;
  return thread_current()->nice_value ;
}

/* Returns 100 times the system load average. */
int
thread_get_load_avg (void) 
{
  return fixedpt_to_int_round_near(mul_float_int(load_avg, 100));
}

/* Returns 100 times the current thread's recent_cpu value. */
int
thread_get_recent_cpu (void) 
{
  struct thread* current_thread = thread_current();
  return fixedpt_to_int_round_near(mul_float_int(current_thread->recent_cpu, 100));
}

void update_all_priorities(void){
  struct list_elem* cur;
  for(cur = list_begin(&all_list); cur != list_end(&all_list); cur=list_next(cur)){
    struct thread* cur_th = list_entry(cur, struct thread, allelem);
    if(cur_th == idle_thread || cur_th == scheduler_thread || cur_th == wakeup_thread){
      continue;
    }
    thread_update_priority(cur_th);
  }
}

void scheduler_manager(void *aux UNUSED){
  scheduler_thread = thread_current();
  while(true){
    enum intr_level old_level = intr_disable ();
    thread_block ();
    intr_set_level (old_level);
    update_load_avg();
    struct list_elem* cur;
    for(cur = list_begin(&all_list); cur != list_end(&all_list); cur=list_next(cur)){
      struct thread* cur_th = list_entry(cur, struct thread, allelem);
      if(cur_th == idle_thread || cur_th == scheduler_thread || cur_th == wakeup_thread){
        continue;
      }
      update_recent_cpu(cur_th);
      thread_update_priority(cur_th);
    }
  }
}

/* Idle thread.  Executes when no other thread is ready to run.

   The idle thread is initially put on the ready list by
   thread_start().  It will be scheduled once initially, at which
   point it initializes idle_thread, "up"s the semaphore passed
   to it to enable thread_start() to continue, and immediately
   blocks.  After that, the idle thread never appears in the
   ready list.  It is returned by next_thread_to_run() as a
   special case when the ready list is empty. */
static void
idle (void *idle_started_ UNUSED) 
{
  struct semaphore *idle_started = idle_started_;
  idle_thread = thread_current ();
  sema_up (idle_started);

  for (;;) 
    {
      /* Let someone else run. */
      intr_disable ();
      thread_block ();

      /* Re-enable interrupts and wait for the next one.

         The `sti' instruction disables interrupts until the
         completion of the next instruction, so these two
         instructions are executed atomically.  This atomicity is
         important; otherwise, an interrupt could be handled
         between re-enabling interrupts and waiting for the next
         one to occur, wasting as much as one clock tick worth of
         time.

         See [IA32-v2a] "HLT", [IA32-v2b] "STI", and [IA32-v3a]
         7.11.1 "HLT Instruction". */
      asm volatile ("sti; hlt" : : : "memory");
    }
}

/* Function used as the basis for a kernel thread. */
static void
kernel_thread (thread_func *function, void *aux) 
{
  ASSERT (function != NULL);

  intr_enable ();       /* The scheduler runs with interrupts off. */
  function (aux);       /* Execute the thread function. */
  thread_exit ();       /* If function() returns, kill the thread. */
}

/* Returns the running thread. */
struct thread *
running_thread (void) 
{
  uint32_t *esp;

  /* Copy the CPU's stack pointer into `esp', and then round that
     down to the start of a page.  Because `struct thread' is
     always at the beginning of a page and the stack pointer is
     somewhere in the middle, this locates the curent thread. */
  asm ("mov %%esp, %0" : "=g" (esp));
  return pg_round_down (esp);
}

/* Returns true if T appears to point to a valid thread. */
static bool
is_thread (struct thread *t)
{
  return t != NULL && t->magic == THREAD_MAGIC;
}

/* Does basic initialization of T as a blocked thread named
   NAME. */
static void
init_thread (struct thread *t, const char *name, int priority)
{
  ASSERT (t != NULL);
  ASSERT (PRI_MIN <= priority && priority <= PRI_MAX);
  ASSERT (name != NULL);

  memset (t, 0, sizeof *t);
  t->status = THREAD_BLOCKED;
  strlcpy (t->name, name, sizeof t->name);
  list_init(&t->lock_acquired);
  t->stack = (uint8_t *) t + PGSIZE;
  t->priority = priority;
  t->priority_before_donation = priority;
  t->seeking = NULL;
  t->magic = THREAD_MAGIC;
  if(t==initial_thread){
    t->nice_value = 0;
  } else {
    t->nice_value = thread_current()->nice_value;
  }
  
<<<<<<< thread.c
<<<<<<< thread.c
  #ifdef USERPROG
    sema_init (&t->sema_ready, 0);
    sema_init (&t->sema_terminated, 0);
    sema_init (&t->sema_ack, 0);
    t->return_status = -1;
    t->load_complete = false;
    int i;
    for(i=0;i<MAX_FILES;i++){
      t->open_files[i] = NULL;
    }
    
  #endif
  if(t != initial_thread){
    page_table_init(t->page_table);
  }
  t->file_executable = NULL;
=======
>>>>>>> 1.14
=======
  #ifdef USERPROG
    sema_init (&t->sema_ready, 0);
    sema_init (&t->sema_terminated, 0);
    sema_init (&t->sema_ack, 0);
    t->return_status = -1;
    t->load_complete = false;
    int i;
    for(i=0;i<MAX_FILES;i++){
      t->open_files[i] = NULL;
    }
    
  #endif
  t->file_executable = NULL;
>>>>>>> 1.20
  t->recent_cpu = 0;
  list_push_back (&all_list, &t->allelem);
}

/* Allocates a SIZE-byte frame at the top of thread T's stack and
    returns a pointer to the frame's base. */
static void * alloc_frame (struct thread *t, size_t size) 
{
  /* Stack data is always allocated in word-size units. */
  ASSERT (is_thread (t));
  ASSERT (size % sizeof (uint32_t) == 0);

  t->stack -= size;
  return t->stack;
}

/* Chooses and returns the next thread to be scheduled.  Should
   return a thread from the run queue, unless the run queue is
   empty.  (If the running thread can continue running, then it
   will be in the run queue.)  If the run queue is empty, return
   idle_thread. */
static struct thread *
next_thread_to_run (void) 
{
  if (list_empty (&ready_list)) {
    return idle_thread;
  }
  else {
    // return list_entry (list_pop_front (&ready_list), struct thread, elem);
    /* taking out the thread having maximum priority */
    struct list_elem *e = list_max (&ready_list, priority_encoder, NULL);
    list_remove (e);
    return list_entry (e, struct thread, elem);
  }
}

/* Completes a thread switch by activating the new thread's page
   tables, and, if the previous thread is dying, destroying it.

   At this function's invocation, we just switched from thread
   PREV, the new thread is already running, and interrupts are
   still disabled.  This function is normally invoked by
   thread_schedule() as its final action before returning, but
   the first time a thread is scheduled it is called by
   switch_entry() (see switch.S).

   It's not safe to call printf() until the thread switch is
   complete.  In practice that means that printf()s should be
   added at the end of the function.

   After this function and its caller returns, the thread switch
   is complete. */
void
schedule_tail (struct thread *prev) 
{
  struct thread *cur = running_thread ();
  
  ASSERT (intr_get_level () == INTR_OFF);

  /* Mark us as running. */
  cur->status = THREAD_RUNNING;

  /* Start new time slice. */
  thread_ticks = 0;

#ifdef USERPROG
  /* Activate the new address space. */
  process_activate ();
#endif

  /* If the thread we switched from is dying, destroy its struct
     thread.  This must happen late so that thread_exit() doesn't
     pull out the rug under itself.  (We don't free
     initial_thread because its memory was not obtained via
     palloc().) */
  if (prev != NULL && prev->status == THREAD_DYING && prev != initial_thread) 
    {
      ASSERT (prev != cur);
      palloc_free_page (prev);
    }
}

/* Schedules a new process.  At entry, interrupts must be off and
   the running process's state must have been changed from
   running to some other state.  This function finds another
   thread to run and switches to it.

   It's not safe to call printf() until schedule_tail() has
   completed. */

static void
schedule (void) 
{
  struct thread *cur = running_thread ();
  struct thread *next = next_thread_to_run ();
  struct thread *prev = NULL;

  ASSERT (intr_get_level () == INTR_OFF);
  ASSERT (cur->status != THREAD_RUNNING);
  ASSERT (is_thread (next));

  if (cur != next)
    prev = switch_threads (cur, next);
  schedule_tail (prev); 
}

/* Returns a tid to use for a new thread. */
static tid_t
allocate_tid (void) 
{
  static tid_t next_tid = 1;
  tid_t tid;

  lock_acquire (&tid_lock);
  tid = next_tid++;
  lock_release (&tid_lock);

  return tid;
}

/* Offset of `stack' member within `struct thread'.
   Used by switch.S, which can't figure it out on its own. */
uint32_t thread_stack_ofs = offsetof (struct thread, stack);


/* Newly added functions */
/* Block thread till next wakeup time.*/
void thread_block_till(int64_t current_time, int64_t wakeup_time){
  /* Disables the interrupt and stores previous value */ 
  enum intr_level prev_intr_value;
  /* Gets current thread */
  struct thread *current_thread = thread_current();
  
  if(current_time > wakeup_time){
    return ;
  }
  
  /* Making sure thread is running */
  ASSERT(current_thread->status == THREAD_RUNNING);
  lock_acquire(&sleepers_lock);
  /* Setting wakeup time of thread and updating next_wakeup_time. 
     Also interrupt needs to be set at previous intr_value. */
  current_thread->wakeup_time = wakeup_time;
  next_wakeup_time = min(next_wakeup_time, wakeup_time);
  list_insert_ordered (&sleeping_threads, &(current_thread->elem), sleeping_encoder, NULL);
  prev_intr_value = intr_disable();
  lock_release(&sleepers_lock);
  thread_block();
  intr_set_level(prev_intr_value);
}


/*Makes thread priority high temporarily to bring it in front of queue*/
void thread_priority_temporarily_up(){
  thread_current()->actual_priority = thread_current()->priority;
  thread_current()->priority = PRI_MAX;
  // thread_set_priority(PRI_MAX);
}

/*Sets pointer to thread to be next waken up in sleepers*/
void thread_set_next_wakeup(){
  /* Do nothing if sleepers is empty */
  if(list_empty(&sleeping_threads)){
    return;
  }
  /* Get begin of sleepers */
  int64_t current_time = timer_ticks();
  struct list_elem *current_top_sleeping;
  struct thread *sleeping_threads_head;
  while(!list_empty(&sleeping_threads)){
    current_top_sleeping = list_begin(&sleeping_threads);
    sleeping_threads_head = list_entry(current_top_sleeping, struct thread, elem);
    if(sleeping_threads_head->wakeup_time <= current_time){
      /*Pop the thread o be waken up*/
      list_pop_front(&sleeping_threads);
      thread_unblock(sleeping_threads_head);
    }
    else{
      break;
    }
  }
  if(list_empty(&sleeping_threads)){
    next_wakeup_time = INT64_MAX;
  }
  else {
    struct thread *new_current_sleeping = list_entry(list_begin(&sleeping_threads), struct thread, elem);
    /* Update next_wakeup_time to next node */
    next_wakeup_time = new_current_sleeping->wakeup_time;
  }
  struct list_elem *current_top_ready = list_max(&ready_list, priority_encoder, NULL);
  struct thread *ready_threads_head;
  ready_threads_head = list_entry(current_top_ready, struct thread, elem);
  if(ready_threads_head->priority > thread_current()->priority){
    thread_yield();
  }
}

/*Retores thread prioirty after it has utilised its CPU timer ticks*/
void thread_priority_restore(){
  // thread_set_priority(thread_current()->actual_priority);
  thread_current()->priority = thread_current()->actual_priority;
}

/* function used for handling donation of priority */
void donate_priority(struct thread* t){
  // if its not seeking anything, return.
  if(t->seeking == NULL){
    return;
  }

  struct lock* ini_lock = t->seeking;
  struct thread* nxt_thread = NULL;
  // loop till thread priority is greater than priority of max of waiting threads for lock/semaphore
  while(ini_lock && t->priority > ini_lock->max_seeking_priority){
    nxt_thread = ini_lock->holder;
    if(nxt_thread == NULL) {
      return;
    }
    // nxt_thread->priority_before_donation = nxt_thread->priority;
    /* setting the priority of the lock and thread to maximum priority */
    ini_lock->max_seeking_priority = t->priority;
    nxt_thread->priority = t->priority;
    /* next lock to be released */
    ini_lock = nxt_thread->seeking;
  }
}

/* function used for updating the thread priorities either to original
   or the maximum of priorities of lock it has acquired */
void update_priority_on_release(struct thread* t){
  int max_priority = t->priority_before_donation;
  /* if it has no acquired locks, then restore its original priority */
  if (list_empty(&t->lock_acquired)){
    t->priority = max_priority;
    return;
  }
  /* else take the maximum of priorities of lock it has acquired and original priority */
  struct list_elem* th = list_max(&t->lock_acquired, lock_encoder, NULL);
  struct lock* xp = list_entry(th, struct lock, elem);
  int max_lock_priority = xp->max_seeking_priority;
  t->priority = max(max_priority, max_lock_priority);
}

static void wakeup_manager(void *aux UNUSED){
  wakeup_thread = thread_current();
  while(true){
    // thread_set_next_wakeup();
    enum intr_level old_level = intr_disable();
    thread_block();
    intr_set_level(old_level);
    thread_set_next_wakeup();
  }
}

bool get_thread_dyingstat_by_tid (tid_t tid) {
  struct list_elem *iter;
  struct thread *ret=NULL, *t = thread_current();
  for (iter = list_begin (&all_list); iter != list_end (&all_list); iter = list_next (iter)){
    ret = list_entry (iter, struct thread, allelem);
    ASSERT (is_thread (ret));
    if (ret->tid == tid && ret->status != THREAD_DYING){
      return true;
    }
  } 
  return false;
}

struct thread* get_thread_by_tid (tid_t tid) {
  struct list_elem *iter;
  struct thread *ret=NULL, *t = thread_current();
  if(list_empty(&all_list)){
    return NULL;
  }
  for (iter = list_begin (&all_list); iter != list_end (&all_list); iter = list_next (iter)){
    ret = list_entry (iter, struct thread, allelem);
    ASSERT (is_thread (ret));
    if (ret->tid == tid){
      return ret;
    }
  } 
  return NULL;
}
