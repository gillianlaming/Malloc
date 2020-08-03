/*
******************************************************************************
*                               mm.c                                         *
*           64-bit struct-based implicit free list memory allocator          *
*                      without coalesce functionality                        *
*                 CSE 361: Introduction to Computer Systems                  *
*                                                                            *
*  ************************************************************************  *
*           segregated list  with best-fit policy        
*                                                                            *
*  ************************************************************************  *
*  ** ADVICE FOR STUDENTS. **                                                *
*  Step 0: Please read the writeup!                                          *
*  Step 1: Write your heap checker. Write. Heap. checker.                    *
*  Step 2: Place your contracts / debugging assert statements.               *
*  Good luck, and have fun!                                                  *
*                                                                            *
******************************************************************************
*/

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
// #define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*sizeof(word_t);       // double word size (bytes)
static const size_t min_block_size = 4*sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

typedef struct block
{
  /* Header contains size + allocation flag */
  word_t header;
  /*
   * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
  char payload[0];
  /*
   * We can't declare the footer as part of the struct, since its starting
   * position is unknown
   */
} block_t;

typedef struct free_block
{
  word_t header;
  
  //block pointers to the prev and next free blocks in the list
  struct free_block * prev_block;
  struct free_block * next_block;
 
  //cant allocate the footer yet
  

} free_block_t;



/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;
static void *seg_list_start = NULL; 
//#define I_CHANGE 10
#define NUM_LISTS 30




bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(free_block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static void place_free(free_block_t *block, size_t size);
static void remove_free(free_block_t *block);
static free_block_t *seg_list(void *address, int index);
static int find_index(size_t size);
static void print_block(block_t * block);


/*
 * performs necesary initializations, including allocating initial heap area.
 * returns false if there was any issue with init, true otherwise
 */
bool mm_init(void) 
{
  dbg_printf("\n\n ------------------mm_init------------\n");
  /*allocate enough space for the pointer to the first block in each seglist 
    size class */
  seg_list_start = (word_t *) (mem_sbrk(wsize*NUM_LISTS));
  int list_index;
  for (list_index = 0; list_index < NUM_LISTS; list_index++) {
    
    *((word_t **)seg_list_start+list_index) = NULL;
  }
    
  // Create the initial empty heap 
  word_t *start = (word_t *)(mem_sbrk(2*wsize));

  if (start == (void *)-1) 
    {
      return false;
    }
  
  dbg_printf("address of epilogue header %p\n", (void*) (&start[1]));
  start[0] = pack(0, true); // Prologue footer
  start[1] = pack(0, true); // Epilogue header
  //debug 16 byte align?
  // Heap starts with first "block header", currently the eipilogue header
  
  heap_start = (block_t *) &(start[1]);

    
  // Extend the empty heap with a free block of chunksize bytes
  if (extend_heap(chunksize) == NULL)
    {
      return false;
    }
  
    
  /*
   * need to initialize the first free block in the list
   * both pointers should point to it because it's the 
   * only free block in the list
   */
    
  return true;
}

/*
 * allocates a block payload of size size bytes.
 * allocated block lies within heap and does not overlap any 
 * other allocated chunk.
 * returns pointer to allocated block.
 */
void *malloc(size_t size) 
{
  dbg_printf("\n\n malloc------------------- %li\n\n", size);
  dbg_requires(mm_checkheap(__LINE__));
  size_t asize;      // Adjusted block size
  size_t extendsize; // Amount to extend heap if no fit is found
  block_t *block;
  void *bp = NULL;
  
    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
      
      mm_init();
    }
  
  if (size == 0) // Ignore spurious request
    {
      
      dbg_ensures(mm_checkheap(__LINE__));
      return bp;
    }

  // Adjust block size to include overhead and to meet 
  //alignment requirements
  asize = max(round_up(size + dsize, dsize), min_block_size);
  dbg_printf("malloc asize: %zu \n", asize);
  // Search the free list for a fit
  block =find_fit(asize);
    
  // If no fit is found, request more memory, and then and place the block
  if (block == NULL)
    {  
      extendsize = max(asize, chunksize);
      block = extend_heap(extendsize);
      if (block == NULL) // extend_heap returns an error
        {
	  return bp;
        }

    }

  place(block, asize);
  bp = header_to_payload(block);
  dbg_ensures(mm_checkheap(__LINE__));
  return bp;
} 

/*
 * frees block that *bp points to.
 * will only work if *bp is result of 
 * malloc() or realloc() call (and has not been freed).
 1 */
void free(void *bp)
{
  dbg_printf("\n\n free------------------- %p\n\n", bp);
  dbg_ensures(mm_checkheap(__LINE__));
  if (bp == NULL)
    {
      return;
    }

  block_t *block = payload_to_header(bp); //allocated block
  size_t size = get_size(block);
  //  dbg_printf("%i\n",__LINE__);
  size = round_up(size, dsize);
  write_header(block, size, false);
  write_footer(block, size, false);
    
  place_free((free_block_t *)block, size);
  coalesce((free_block_t *)block);
  dbg_ensures(mm_checkheap(__LINE__));

}

/*
 * changes size of memory block pointed to by ptr.
 * if the address is different and realloc() was 
 * successful, then old block was freed
 * returns pointer to allocated region of size bytes.
 */
void *realloc(void *ptr, size_t size)
{
  size_t asize, csize, bsize;
  block_t *block = payload_to_header(ptr); //allocated
  csize = get_size(block);
  dbg_printf("\n\n realloc-------------------\nblock at %p from %li to %li\n",
	     block, csize, size);
  dbg_requires(mm_checkheap(__LINE__));
  
  
  void *newptr;
  block_t *block_next;
       
  if (size == 0)
    {
      free(ptr);
      return NULL;
    }
  // If ptr is NULL, then equivalent to malloc
  if (ptr == NULL)
    {
      return malloc(size);
    }
  
  asize = round_up(size+dsize, dsize); //this is NOT just payload
 
   
  if (asize == csize){
    return ptr;
  }
    
  if (asize + min_block_size <= csize){
    // we can put the new block where the old block is and coalesce
    // the remainder of the o.g. block
       
    write_header(block, asize, true);
    write_footer(block, asize, true);
    
    block_next = find_next(block);
    dbg_assert((csize-asize)%dsize == 0);
      //nsize = round_up((csize - asize), dsize);
    write_header(block_next, csize-asize, false);
    write_footer(block_next, csize-asize, false);
    
    place_free((free_block_t *)block_next, csize-asize);
    coalesce((free_block_t *) block_next);
    dbg_requires(mm_checkheap(__LINE__));
    return ptr;
  }
    
  else if (asize > csize){
      
    block_next = find_next(block);
      
    if (!get_alloc(block_next) && get_size(block_next) + csize >= asize){
      
      size_t next_size = get_size(block_next);

      //if the combined two blocks can fit the new block
      
      bsize = csize + next_size - asize;
      remove_free((free_block_t *) block_next);
      
      //want to coalesce
      if (bsize >= min_block_size){
	
	write_header(block, asize, true);
	write_footer(block, asize, true);
	
	block_next = find_next(block); 
	dbg_assert((bsize % dsize) == 0);
	write_header(block_next, bsize, false);
	write_footer(block_next, bsize, false);
	
	place_free((free_block_t *)block_next, bsize);
	
	dbg_requires(mm_checkheap(__LINE__));
	return ptr;
      }
      else {

	write_header(block, csize + next_size, true);
	write_footer(block, csize + next_size, true);
	dbg_requires(mm_checkheap(__LINE__));
	return ptr;
      }
      
    }
    else{
      newptr = malloc(size);
      // If malloc fails, the original block is left untouched
      if (newptr == NULL)
	{
	  return NULL;
	}
      
      size_t copysize = get_payload_size(block); // gets size of old payload
      dbg_ensures(size >= copysize);
     
      memcpy(newptr, ptr, copysize);

      // Free the old block
      free(ptr);
      dbg_requires(mm_checkheap(__LINE__));
      return newptr;

    }
  }

  dbg_printf("here\n");
  dbg_requires(mm_checkheap(__LINE__));
  return ptr;
}

/*
 * contiguously allocates enough space for count
 *  objects that are size bytes of memory each and returns a pointer to
 * the allocated memory.  The allocated memory is filled with bytes of
 *  value zero.
 */
void *calloc(size_t elements, size_t size)
{
  void *bp;
  size_t asize = elements * size;

  if (asize/elements != size)
    {    
      // Multiplication overflowed
      return NULL;
    }
    
  bp = malloc(asize);
  if (bp == NULL)
    {
      return NULL;
    }
  // Initialize all bits to 0
  memset(bp, 0, asize);

  return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * extends the heap by size bytes
 * creates a new free block and places it on appropriate list
 * TODO: do we want this to return a block_t or free_block_t
 */
static block_t *extend_heap(size_t size) 
{
  void *bp;

  // Allocate an even number of words to maintain alignment
  
  size = max(round_up(size, dsize), min_block_size);

 
  if ((bp = mem_sbrk(size)) == (void *)-1)
    {
      return NULL;
    }
    
  
  // Initialize free block 
  block_t *block = payload_to_header(bp);
  dbg_printf("line number : %i\n", __LINE__);
  write_header(block, size, false);
  write_footer(block, size, false);
  
  // Create new epilogue header
  block_t *block_next = find_next(block);
  write_header(block_next, 0, true);
  
  place_free((free_block_t *)block, size);

  // Coalesce in case the previous block was free
  return coalesce((free_block_t *)block);
}

/*
 * merge free blocks if neccessary.
 * checks allocation of blocks coming before and after the
 * block passed through as a param.
 */
static block_t *coalesce(free_block_t * block) 
{
  
  /* we have three blocks: let's call them A,
     B, C */
  /* we need to check the allocation of all
     three */
  //dbg_requires(mm_checkheap(__LINE__));
  
  block_t * A_block = find_prev((block_t *)block);
  block_t * C_block = find_next((block_t *)block);
  
  bool A_alloc = get_alloc(A_block);
  bool C_alloc = get_alloc(C_block);

  //dbg_printf("A_block %p\n", A_block);
  print_block(A_block);
  print_block((block_t *)block);
  print_block(C_block);
  //dbg_printf("B_block %p\n", block);
  //dbg_printf("C_block %p\n", C_block);
  
  size_t new_size = extract_size(block->header);
  
  //case 1: allocated, freed, allocated
  if (A_alloc && C_alloc){
    dbg_printf("line number: %i\n", __LINE__); 
    return (block_t *)block;
  }
  //special case from piazza
  if(A_block == (block_t *)block){
    if(!C_alloc){
      remove_free(block);
      remove_free((free_block_t *) C_block);
      new_size += get_size(C_block);
      dbg_printf("line number: %i\n", __LINE__); 
      write_header((block_t *) block, new_size, false); 
      write_footer((block_t *) block, new_size, false);
       place_free(block, new_size);
      }
    dbg_printf("line number: %i\n", __LINE__); 
    return (block_t *)block;
  }
  
  //case 2: allocated, freed, free
  if (A_alloc && (!C_alloc)){
    remove_free(block);
    remove_free((free_block_t *) C_block);
    new_size += get_size(C_block);
    dbg_printf("line number: %i\n", __LINE__); 
    write_header((block_t *) block, new_size, false); 
    write_footer((block_t *) block, new_size, false); 
  }
  
  //case 3: free, freed, allocated
  if ((!A_alloc) && C_alloc){ 
    remove_free(block);
    remove_free((free_block_t *) A_block);
    new_size += get_size(A_block);
    dbg_printf("line number: %i\n", __LINE__); 
    write_header((block_t *) A_block, new_size, false); 
    write_footer((block_t *) block, new_size, false);
    block = (free_block_t *)A_block;
  }
    
  //case 4: free, freed, free
  if ((!A_alloc) && (!C_alloc)){
    remove_free(block);
    remove_free((free_block_t *) C_block);
    remove_free((free_block_t *) A_block);
    new_size += get_size(A_block) + get_size(C_block);
    dbg_printf("line number: %i\n", __LINE__); 
    write_header((block_t *) A_block, new_size, false); 
    write_footer(A_block, new_size, false); 
    block = (free_block_t *)A_block;
  }
  
  place_free(block, new_size);
  
  return (block_t *)block;
}

/*
 * after finding the block in memory where a 
 * new block can be placed, place actually 
 * puts it in memory and writes the appropriate
 * headers and footers
 */
static void place(block_t *block, size_t asize)
{
  size_t nsize;
  remove_free((free_block_t *) block);
  size_t csize = get_size(block);
  
  if ((csize - asize) >= min_block_size)
    {
      block_t *block_next;
      dbg_printf("%i\n", __LINE__);
      write_header(block, asize, true);
      write_footer(block, asize, true);
      
      block_next = find_next(block);
      nsize = csize-asize;
      dbg_assert(!(nsize % 16));
      dbg_printf("%i\n", __LINE__);
      write_header(block_next, nsize, false);
      write_footer(block_next, nsize, false);
      
      place_free((free_block_t *) block_next, (nsize));
      coalesce((free_block_t *) block_next);
      
    }

  else
    { 
      write_header(block, csize, true);
      write_footer(block, csize, true);
    }
}

/*
 * takes in a pointer to a block that is going to be free
 * finds the correct free list to put it on and adds it
 * sets next and prev free blocks accordingly
 * extend heap, free, coalesce (?)
 */
static void place_free(free_block_t *block, size_t size)
{
  dbg_assert(size >= min_block_size);
  dbg_assert(!get_alloc((block_t*)block));
  
  int list_index = find_index(size);
  free_block_t * start = (free_block_t *)seg_list(seg_list_start, list_index);
    
  //free_block_t *listp = start;
  
  if (start == NULL){
    block->prev_block = block;
    block->next_block = block;
    ((free_block_t **)seg_list_start)[list_index] = block;
    return;
  }
  
  start->prev_block->next_block = block;
  block->prev_block = start->prev_block;
  block->next_block = start;
  start->prev_block = block;
  
  return;
}

/*
 * given a free block, remove it from the seglist of free blocks
 * 
 */
static void remove_free(free_block_t *block)
{
  
  size_t size = extract_size(block->header);
  int list_index = find_index(size);
  write_header((block_t *)block, size, true);
  write_footer((block_t *) block, size, true); 
  
  //block was the only thing in list
  if (block->next_block == block){
    dbg_assert(block->next_block == block->prev_block);
    ((free_block_t **)seg_list_start)[list_index] = NULL;
    return;
  }
  block->prev_block->next_block = block->next_block;
  block->next_block->prev_block = block ->prev_block;
  if((free_block_t *)seg_list(seg_list_start, list_index) == block){
    ((free_block_t **)seg_list_start)[list_index] = block->next_block;
  }
  return;
  
}

//finding correct index in array given the size
static int find_index(size_t size)
{
  int list_index = 0;
   while (list_index < (NUM_LISTS - 1) && size > 32) {
    size = size >> 1;
    list_index++;
  }
  return list_index;
}

/*
 * takes in the size of the block.
 * needs to then search the appropriate free list.
 * if no block is found, go up one size until u find one 
 */
static block_t *find_fit(size_t asize)
{
  
  int list_index = find_index(asize);
  free_block_t * start;
  free_block_t * rover;
  while(list_index < NUM_LISTS) {
    start  = (free_block_t *) seg_list(seg_list_start, list_index);
    if (start == NULL){
      list_index++;
      continue;
    }
    rover = start;
    do{
      if (asize <= extract_size(rover->header)){
	//flag = true;
	return (block_t *)rover;
      }
      rover = rover->next_block;
    }while(rover != start);
    list_index++;
  }
  return NULL; 
}

/*My heap checker checks the following:
 * Is every block in the free list marked as free?
 * Are there any contiguous free blocks that somehow escaped coalescing?
 * Is every free block actually in the free list?
 * Do the pointers in the free list point to valid free blocks?
 * Do any allocated blocks overlap?
 * Do the pointers in a heap block point to valid heap addresses?
 * Check to make sure headers and footers are the same & 
 * point to a block with the correct size
 */
bool mm_checkheap(int line)  
{ 
  dbg_printf("checking the heap!\n");
  // dbg_printf("min block size %zu \n", min_block_size);
  free_block_t * start;
  int i, list_number;
  free_block_t * rover;

  //loop thru every block in each seglist  
  for (i = 0; i < NUM_LISTS; i++){
    start = (free_block_t *)seg_list(seg_list_start, i);
    if(start == NULL){
      continue;
    }
    rover = start;
   do{
       if (extract_alloc(rover->header)){
	dbg_printf("Free block marked as allocated!\n");
	dbg_printf("list index of bad block: %d\n",i);
	dbg_printf("line %i\n",line);
	print_block((block_t *)rover);
	return false;
      }
      if ((rover -> next_block == rover)&&(rover != start)){
	dbg_printf("CYcyle exists in free list %i at line  %i\n", i, line);
	return false;
      }
      rover = rover->next_block;
   }while(rover != start);
    
  }
  ///
    block_t *next = NULL;
    block_t * block = heap_start;
    while ((block != NULL) && get_size(block) ) {
      next = find_next(block);

      //check if two continuous free blocks escaped coalescing
      if ((!get_alloc(block) && !get_alloc(next))) {
	dbg_printf("\nTwo continuous blocks escaped coalescing %i\n", line);
	print_block(block);
	print_block(next);
	return false;
      } 

      //alignment check 
       if ((word_t)block->payload % dsize) {
	 dbg_printf("Block is not 16 byte aligned%i \n", line);
	 print_block(block);
	 return false;
      }
       
      word_t * footer = find_prev_footer(next);
      
       //check if footer/header information match
      if ((block->header) != *find_prev_footer(next)) {	 
	 dbg_printf("\nheader/footer size do not match: %i\n",line);
	 dbg_printf("header 0x%016lx \n", block->header);
	 dbg_printf("footer  0x%016lx \n", *find_prev_footer(next));
	 
	 print_block(block);
	 return false;
      }    
       //check if allocations match
       if (get_alloc(block) != extract_alloc(*footer)) {
	 dbg_printf("\nheader/footer do not match: %i\n",line);
	 dbg_printf("footer %p\n",footer);
	 print_block(block);
	 return false;
      }
      
       
       //if this is a free block, check if it is in seg_list
      if (!get_alloc(block)) {
	bool flag = false;
	list_number = find_index(get_size(block));
	start = (free_block_t *)seg_list(seg_list_start, list_number);
	dbg_assert(start != NULL);
	
	rover = start;
	do{
	  if (rover == (free_block_t*) block) {
	    flag = true;
	  }
	  rover = rover->next_block;
	}while (rover != start);
	if (!flag) {
	  dbg_printf("free block not in the seg_list %i\n", line);
	  dbg_printf("list number %i\n", list_number);
	  print_block(block);
	  return false;
	}
      }
      block = find_next(block);
    }
    dbg_printf("checkheap passed!\n");
   return true;
}
/*prints out relevent block DEETS
 */
static void print_block(block_t * block)
{
  dbg_printf("Block: %p \n", (void*)block);
  dbg_printf("alloc: \t%s \n", get_alloc(block) ? "true" : "false");
  dbg_printf("size: %zu \n", get_size(block));
  if (!get_alloc(block)){
   
    dbg_printf("seg list index %i\n", find_index(get_size(block)));
  }
  dbg_printf("\n");

  return;
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
  return (x > y) ? x : y;
}

/*
 * given a pointer to an address in memory and 
 * an index into the array, return the start 
 * address of the seg_list 
 *
 */
static free_block_t *seg_list(void* address, int index)
{
  return ((free_block_t **)address)[index];
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
  return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
  word_t hello =  alloc ? (size | alloc_mask) : size;
  dbg_printf("size 0x%lx alloc %s generate header 0x%016lx \n", size, alloc ? "true" : "false", hello);
  return hello;
    
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
  return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
  return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
  size_t asize = get_size(block);
  return asize - dsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
  return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
  return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
  dbg_printf("writing header for block at %p \n", block);
  block->header = pack(size, alloc);
}




/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
  dbg_printf("writing footer for block at %p \n", block);
  word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
  dbg_printf("footer addy %p \n", footerp);
  *footerp = pack(size, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
  dbg_requires(block != NULL);
  block_t *block_next = (block_t *)(((char *)block) + get_size(block));

  dbg_ensures(block_next != NULL);
  return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
  // Compute previous footer position as one word before the header
  return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
  word_t *footerp = find_prev_footer(block);
  size_t size = extract_size(*footerp);
  return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 * 
 * block type it is going to return.
 */
static block_t *payload_to_header(void *bp)
{
  return (block_t *)(((char *)bp) - offsetof(block_t, payload));
  //return (block_t *)(((char *)bp) - wsize);
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
  return (void *)(block->payload);
}

