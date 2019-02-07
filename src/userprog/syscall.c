#include "userprog/syscall.h"
#include <stdio.h>
#include <string.h>
#include <syscall-nr.h>
#include "threads/interrupt.h"
#include "threads/thread.h"
#include "threads/vaddr.h"
#include "userprog/pagedir.h"
#include "threads/init.h"

#define SYS_CALLS 13

typedef struct system_calls{
  int type;
  int args;
  int arg_type[4];
  void (*function_void) ();
  int (*function_int) ();
} system_calls;

static struct lock file_secure;
static void syscall_handler (struct intr_frame *);

static void halt(void);
static int exec(char*);
static int wait(int);
static int create(char*, int);
static int remove(char*);
static int open(char*);
static int filesize(int);
static int read(int, void*, int);
static int write(int, void*, int);
static void seek(int, int);
static int tell(int );
static void close(int);
static void dummy_void(void);
static int dummy_int(void);
static void check_string(char*);

static void check_valid_address(void *esp);

/* 
   1 - int 
   2 - char* 
   3 - void* 
*/
static system_calls all_calls[SYS_CALLS] = {
  {0, 0, {-1, -1, -1, -1}, halt, dummy_int },
  {0, 1, {1, -1, -1, -1}, exit, dummy_int },
  {1, 1, {2, -1, -1, -1}, dummy_void, exec },
  {1, 1, {1, -1, -1, -1}, dummy_void, wait },
  {1, 2, {2, 1, -1, -1}, dummy_void, create },
  {1, 1, {2, -1, -1, -1}, dummy_void, remove },
  {1, 1, {2, -1, -1, -1}, dummy_void, open },
  {1, 1, {1, -1, -1, -1}, dummy_void, filesize },
  {1, 3, {1, 3, 1, -1}, dummy_void, read },
  {1, 3, {1, 3, 1, -1}, dummy_void, write },
  {0, 2, {1, 1, -1, -1}, seek, dummy_int },
  {1, 1, {1, -1, -1, -1}, dummy_void, tell },
  {0, 1, {1, -1, -1, -1}, close, dummy_int }
};

void
syscall_init (void) 
{
  intr_register_int (0x30, 3, INTR_ON, syscall_handler, "syscall");
  lock_init(&file_secure);
}

static void
syscall_handler (struct intr_frame *f) 
{
  // printf ("system call!\n");
  void *esp = f->esp;
  check_valid_address(esp);
  int syscall_typenum = *((int *)esp);
  esp += sizeof(int);
  check_valid_address(esp);
  const int total_syscalls = sizeof(all_calls)/sizeof(all_calls[0]);
  system_calls action;
  int* pointers[4];
  int int_param[4] = {0};
  char* char_param[4];
  void* void_param[4];
  if(syscall_typenum >= 0  && syscall_typenum < total_syscalls){
    action = all_calls[syscall_typenum];
    int i, type;
    // printf("syscall %d %d\n", syscall_typenum, action.args);
    for(i=0;i<action.args;i++){
      check_valid_address(esp);
      type = action.arg_type[i];
      if(type == 1){
        int_param[i] = *((int *)esp);
        pointers[i] = &int_param[i];
      }
      else if(type == 2){
        char_param[i] = *((char **)esp);
        pointers[i] = &char_param[i];
      }
      else{
        void_param[i] = *((void **)esp);
        pointers[i] = &void_param[i];
      }
      esp += sizeof(int);
    }
    if(action.type == 0){
      if(action.args == 0){
        action.function_void();
      }
      else if(action.args == 1){
        action.function_void(*pointers[0]);
      }
      else if(action.args == 2){
        action.function_void(*pointers[0], *pointers[1]);
      }
      else if(action.args == 3){
        action.function_void(*pointers[0], *pointers[1], *pointers[2]);
      }
      else{
        action.function_void(*pointers[0], *pointers[1], *pointers[2], *pointers[3]);
      }
    }
    else{
      int return_val;
      if(action.args == 0){
        return_val = action.function_int();
      }
      else if(action.args == 1){
        return_val = action.function_int(*pointers[0]);
      }
      else if(action.args == 2){
        return_val = action.function_int(*pointers[0], *pointers[1]);
      }
      else if(action.args == 3){
        return_val = action.function_int(*pointers[0], *pointers[1], *pointers[2]);
      }
      else{
        return_val = action.function_int(*pointers[0], *pointers[1], *pointers[2], *pointers[3]);
      }
      f->eax = return_val;
    }
  }
  else {
    printf("Invalid calling!");
    thread_exit();
  }
}

static void halt(){
  power_off();
}

void exit(int status){
  struct thread* curr_thread = thread_current();
  char *th_name = thread_current()->name, *rem;
  int i;
  for(i=2;i<MAX_FILES;i++){
    if(curr_thread->open_files[i]!=NULL){
      close(i);
    }
  }
  th_name = strtok_r(th_name, " ", &rem);
  printf("%s: exit(%d)\n", th_name, status);
  tid_return_val[curr_thread->tid] = status;
  sema_up (&curr_thread->sema_terminated);
  sema_down(&curr_thread->sema_ack);
  thread_exit();
}

static int exec(char *cmd_line){
	check_valid_address(cmd_line);
	check_string(cmd_line);
  lock_acquire(&file_secure);
	tid_t child_tid = process_execute(cmd_line);
  lock_release(&file_secure);
  struct thread* child_thread = tid_mapping[child_tid];
  if(child_thread == NULL){
    return -1;
  }
  sema_down(&child_thread->sema_ready);
  if(tid_load_complete[child_tid] == 0){
    child_tid = -1;
  }
  return child_tid;
}

static int wait(int pid){
  if(pid<0 || pid>2040) {
    return -1;
  }
  struct thread *child_thread = tid_mapping[pid];

  if(child_thread==NULL) {
    return -1;
  }

  int status=-1;
  if(tid_return_val[pid]==-1) {
    status = -1;
  }
  else{
    sema_down(&child_thread->sema_terminated);
    status = tid_return_val[pid];
    tid_return_val[pid]= -1;
  }

  sema_up(&child_thread->sema_ack);
  return status;
}

static int create(char *file, int initial_size){
  check_valid_address(file);
  check_valid_address(file+initial_size);
  lock_acquire(&file_secure);
  int return_status = filesys_create(file, initial_size);
  lock_release(&file_secure);
  return return_status;
}

static int remove(char *file){
  check_valid_address(file);
  check_string(file);
  lock_acquire(&file_secure);
  int return_status = filesys_remove(file);
  lock_release(&file_secure);
  return return_status;
}

static int open(char *file){
  check_valid_address(file);
  check_string(file);
  lock_acquire(&file_secure);
  struct file *new_file = filesys_open(file);
  lock_release(&file_secure);
  if(new_file == NULL){
    return -1;
  }
  int allocated_fd = -1, i;
  struct thread *curr_thread = thread_current();
  for(i=2;i<MAX_FILES;i++){
    if(curr_thread->open_files[i] == NULL){
      allocated_fd = i;
      curr_thread->open_files[i] = new_file;
      break;
    }
  }
  return allocated_fd;
}

static int filesize(int fd){
  struct thread *curr_thread = thread_current();
  if(fd<2 || fd>=MAX_FILES){
    return 0;
  }
  if(curr_thread->open_files[fd] == NULL){
    return 0;
  }
  lock_acquire(&file_secure);
  int length = file_length(curr_thread->open_files[fd]);
  lock_release(&file_secure);
  return length;
}

static int read(int fd, void *buffer, int size){
  check_valid_address(buffer);
  check_valid_address(buffer+size);
  int file_written = 0;
  struct thread* curr_thread = thread_current();
  if(fd == 0){
    file_written = size;
    lock_acquire(&file_secure);
    int i;
    for(i = 0 ; i < size ; i++){
      *((uint8_t *)buffer+i) = input_getc();
    }
    lock_release(&file_secure);
  }
  else if(fd>1 && fd < MAX_FILES && curr_thread->open_files[fd] != NULL){
    lock_acquire(&file_secure);
    file_written = file_read(curr_thread->open_files[fd], buffer, size);
    lock_release(&file_secure);
  }
  return file_written;
}

static int write(int fd, void *buffer, int size){
  int file_size = 0;
  struct thread* curr_thread = thread_current();
  check_valid_address(buffer);
  check_string(buffer);
  if(fd == 1){
    file_size = size;
    putbuf(((char *)buffer), size);
  }
  else if(fd > 1 && fd < MAX_FILES && curr_thread->open_files[fd] != NULL){
    lock_acquire(&file_secure);
    file_size = file_write(curr_thread->open_files[fd], buffer, size);
    lock_release(&file_secure);
  }
  return file_size;
}

static void seek(int fd, int position){
  struct thread *curr_thread = thread_current();
  if(fd<2 || fd>=MAX_FILES){
    return;
  }
  if(curr_thread->open_files[fd] == NULL){
    exit(-1);
  }
  lock_acquire(&file_secure);
  file_seek(curr_thread->open_files[fd], position);
  lock_release(&file_secure);
}

static int tell(int fd){
  struct thread *curr_thread = thread_current();
  if(fd<2 || fd>=MAX_FILES){
    return -1;
  }
  if(curr_thread->open_files[fd] == NULL){
    return -1;
  }
  lock_acquire(&file_secure);
  int position = file_tell(fd);
  lock_release(&file_secure);
  return position;
}

static void close(int fd){
  struct thread *curr_thread = thread_current();
  if(fd<0 || fd>=MAX_FILES){
    exit(-1);
  }
  if(curr_thread->open_files[fd] == NULL){
    exit(-1);
  }
  lock_acquire(&file_secure);
  file_close(curr_thread->open_files[fd]);
  curr_thread->open_files[fd] = NULL;
  lock_release(&file_secure);
}

static void check_string(char* file_name){
  while(*file_name != '\0'){
    check_valid_address((void *)file_name);
    file_name ++;
  }
}

static void check_valid_address(void *esp){
  uint32_t current_page_dir = thread_current()->pagedir;
  if(esp == NULL || is_user_vaddr(esp)==0 || pagedir_get_page(current_page_dir, esp) == NULL){
    exit(-1);
  }
}

static void dummy_void(void){
}

static int dummy_int(void){
  return 0;
}
