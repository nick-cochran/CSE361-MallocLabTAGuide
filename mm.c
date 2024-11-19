/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based implicit free list memory allocator          *
 *                      without coalesce functionality                        *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                               Nick Cochran                                 *
 *                          email: c.nick@wustl.edu                           *
 *                            Malloc Lab TA Guide                             *
 *                                                                            *
 *                           Implemented Features:                            *
 *                                  Coalesce                                  *
 *                             Explicit Free List                             *
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

/*** PRINTING UTILITIES ***/
#define BLACK   "\033[0;30m"
#define RED     "\033[0;31m"
#define GREEN   "\033[0;32m"
#define BLUE    "\033[0;34m"
#define CYAN    "\033[0;36m"
#define MAGENTA "\033[0;35m"
#define YELLOW  "\033[0;33m"
#define WHITE   "\033[0;37m"

#define BOLD       "\033[1m"
#define UNDERLINE  "\033[4m"
#define RESET   "\033[0m"


/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
// #define DEBUG // *** uncomment this line to enable debugging ***

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
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
    union {
        struct {
            struct block *next;
            struct block *prev;
        };
        /*
         * We don't know how big the payload will be.  Declaring it as an
         * array of size 0 allows computing its starting address using
         * pointer notation.
         */
        char payload[0];
    };
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;


/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL; // Pointer to the first block in the heap
static block_t *free_list_head = NULL; // Pointer to the first block in the explicit free list


/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t word);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t word);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static void list_insert(block_t *block);
static void list_remove(block_t *block);

bool mm_checkheap(int lineno);
bool print_heap();


/**
 * @brief initialize the heap to be used by malloc
 *
 * @Changelog
 * - Provided Function at Init.
 */
bool mm_init(void) 
{
    free_list_head = NULL; // set free list head to NULL for edge case in the code
    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true); // Prologue footer
    start[1] = pack(0, true); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/**
 * @brief overload the malloc function with our implementation
 *
 * @Changelog
 * - Provided Function at Init.
 */
void *malloc(size_t size) 
{
    dbg_printf(BOLD MAGENTA"MALLOC CALLED with size: %lu\n"RESET, size);
    dbg_ensures(print_heap());

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

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

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

/**
 * @brief overload the free function with our implementation
 *
 * @Changelog
 * - Provided Function at Init.
 */
void free(void *bp)
{
    dbg_printf(BOLD CYAN"FREE CALLED with addr: %p\n"RESET, bp);
    dbg_ensures(print_heap());

    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    write_header(block, size, false);
    write_footer(block, size, false);

    coalesce(block);
}

/**
 * @brief overload the realloc function with our implementation
 *
 * @Changelog
 * - Provided Function at Init.
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
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

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief overload the calloc function with our implementation
 *
 * @Changelog
 * - Provided Function at Init.
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

/******** The remaining content below are helper and debug routines ********/;

/**
 * @brief extends the heap with the given size
 *
 * @param size the number of bytes to extend the heap by
 *
 * @return the newly created block
 *
 *
 * @Changelog
 * - Provided Function at Init.
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

/**
 * @brief coalesces the block with its neighbors
 *
 * @param block the black being freed
 *
 * @return the resulting block
 *
 * @Changelog
 * - Provided Function at Init.  Added functionality to it.
 * - Added explicit free list insert and remove.
 */
static block_t *coalesce(block_t * block) 
{
    block_t *prev_block = find_prev(block);
    block_t *next_block = find_next(block);

    size_t block_size = get_size(block);

     // check edge case where previous block is prologue
    bool prev_alloc = prev_block == block ? true : get_alloc(prev_block);
    bool next_alloc = get_alloc(next_block);

    // case 1
    if(prev_alloc && next_alloc) {
        list_insert(block);
        return block;
    }

    size_t next_size = get_size(next_block);

    // case 2
    if(prev_alloc && !next_alloc) {
        block_size += next_size;
        list_remove(next_block);

        write_header(block, block_size, false);
        write_footer(block, block_size, false);

        list_insert(block);
        return block;
    }

    size_t prev_size = get_size(prev_block);

    // case 3
    if(!prev_alloc && next_alloc) {
        block_size += prev_size;
    }
    // case 4
    else {
        block_size += prev_size + next_size;
        list_remove(next_block);
    }
    list_remove(prev_block);

    write_header(prev_block, block_size, false);
    write_footer(prev_block, block_size, false);

    list_insert(prev_block);
    return prev_block;
}

/**
 * @brief splits the block into a block with the given size if it can be split,
 *          else writes the new header and footer for the given block
 *
 * @param block the block being allocated
 * @param asize the required number of bytes
 *
 * @Changelog
 * - Provided Function at Init.
 * - Added explicit free list insert and remove.
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);

    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;
        write_header(block, asize, true);
        write_footer(block, asize, true);
        list_remove(block);

        block_next = find_next(block);
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);
        list_insert(block_next);
    }
    else
    { 
        write_header(block, csize, true);
        write_footer(block, csize, true);
        list_remove(block);
    }
}

/**
 * @brief finds a block that fits the given size
 *
 * @param asize the required number of bytes
 *
 * @return the block that fits the given size, or NULL if no such block exists
 *
 * @Changelog
 * - Provided Function at Init.
 * - Changed to find first block in the explicit free list.
 */
static block_t *find_fit(size_t asize)
{
    block_t *block = free_list_head;

    for(; block != NULL; block = block->next) {
        if(asize <= get_size(block)) {
            return block;
        }
    }

    return NULL; // no fit found
}

/**
 * @brief returns x if x > y, and y otherwise.
 *
 * @param x
 * @param y
 *
 * @return the maximum of x and y
 *
 * @Changelog
 * - Provided Function at Init.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}


/**
 * @brief Rounds size up to next multiple of n
 *
 * @param size
 * @param n
 *
 * @return the rounded up size
 *
 * @Changelog
 * - Provided Function at Init.
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}


/**
 * @brief returns a header reflecting a specified size and its alloc status.
 *        If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 *
 * @param size
 * @param alloc
 *
 * @return the packed word
 *
 * @Changelog
 * - Provided Function at Init.
 */
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | alloc_mask) : size;
}


/**
 * @brief returns the size of a given header value based on the header
 *        specification above.
 *
 * @param word
 *
 * @return the size from the header
 *
 * @Changelog
 * - Provided Function at Init.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}


/**
 * @brief returns the size of a given block by clearing the lowest 4 bits
 *        (as the heap is 16-byte aligned).
 *
 * @param block
 *
 * @return the size of the block
 *
 * @Changelog
 * - Provided Function at Init.
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}


/**
 * @brief returns the payload size of a given block, equal to
 *        the entire block size minus the header and footer sizes.
 *
 * @param block
 *
 * @return the payload size of the block
 *
 * @Changelog
 * - Provided Function at Init.
 */
static size_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
}


/**
 * @brief returns the allocation status of a given header value based
 *        on the header specification above.
 *
 * @param word the header of a block
 *
 * @return 1 if allocated, and 0 if free
 *
 * @Changelog
 * - Provided Function at Init.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}


/**
 * @brief returns true when the block is allocated based on the
 *        block header's lowest bit, and false otherwise.
 *
 * @param block
 *
 * @return 1 if allocated, and 0 if free
 *
 * @Changelog
 * - Provided Function at Init.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}


/**
 * @brief given a block and its size and allocation status,
 *        writes an appropriate value to the block header.
 *
 * @param block
 * @param size
 * @param alloc
 *
 * @Changelog
 * - Provided Function at Init.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block->header = pack(size, alloc);
}


/**
 * @brief given a block and its size and allocation status,
 *        writes an appropriate value to the block footer by first
 *        computing the position of the footer.
 *
 * @param block
 * @param size
 * @param alloc
 *
 * @Changelog
 * - Provided Function at Init.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
}

/**
 * @brief given a payload pointer, returns a pointer to the
 *        corresponding block.
 *
 * @param bp
 *
 * @return a pointer to the corresponding block
 *
 * @Changelog
 * - Provided Function at Init.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/**
 * @brief given a block pointer, returns a pointer to the
 *        corresponding payload.
 *
 * @param block
 *
 * @return a pointer to the payload of the block
 *
 * @Changelog
 * - Provided Function at Init.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}

/**
 * @brief returns the next consecutive block on the heap by adding the
 *        size of the block.
 *
 * @param block
 *
 * @return the next block
 *
 * @Changelog
 * - Provided Function at Init.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}


/**
 * @brief returns the footer of the previous block.
 *
 * @param block
 *
 * @return the footer of the previous block
 *
 * @Changelog
 * - Provided Function at Init.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}


/**
 * @brief returns the previous block position by checking the previous
 *        block's footer and calculating the start of the previous block
 *        based on its size.
 *
 * @param block
 *
 * @return the previous block
 *
 * @Changelog
 * - Provided Function at Init.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/**
 * @brief insert the block at the beginning of the free list
 *
 * @param block the block to be inserted
 *
 * @ChangeLog
 * - Added Function for Explicit Free List.
 */
static void list_insert(block_t *block) {

    // empty free list
    if(free_list_head == NULL) {
        block->prev = NULL;
        block->next = NULL;
        free_list_head = block;
    }
    // at least one item in the free list
    else {
        block->prev = NULL;
        block->next = free_list_head;
        free_list_head->prev = block;
        free_list_head = block;
    }
}

/**
 * @brief remove the block from the free list
 *
 * @param block the block to be removed
 *
 * @ChangeLog
 * - Added Function for Explicit Free List.
 */
static void list_remove(block_t *block) {

    block_t *prev_block = block->prev;
    block_t *next_block = block->next;

    if(prev_block == NULL && next_block == NULL) {
        free_list_head = NULL;
    }
    else if(prev_block == NULL) {
        next_block->prev = NULL;
        free_list_head = next_block;
    }
    else if(next_block == NULL) {
        prev_block->next = NULL;
    }
    else {
        prev_block->next = next_block;
        next_block->prev = prev_block;
    }
}



/**
 * @brief checks the heap for all invariants as shown in the changelog.
 *
 * @param line the line number of the caller
 *
 * @return true if no invariants are violated, false otherwise
 *
 * @Changelog
 * - Provided Function at Init.  Added Coalesce Invariant -- 1.
 * - Added Explicit Free List Invariants -- 2, 3, 4, 5.
 */
bool mm_checkheap(int line)
{

    int free_list_count = 0;
    int heap_count = 0;

    block_t *b;
    // loop through the heap for all invariants requiring the entire heap
    for (b = heap_start; get_size(b) != 0; b = find_next(b)) {
        block_t * prev = find_prev(b);
        block_t * next = find_next(b);

        bool b_alloc = get_alloc(b);
        bool prev_alloc;
        if(prev == heap_start) { // check edge case where previous block is prologue
            prev_alloc = true;
        } else {
            prev_alloc = get_alloc(prev);
        }
        bool next_alloc = get_alloc(next);

        // Check that Coalesce works as intended
        if (b_alloc == false) {
            heap_count++; // increment count of free blocks in the heap

            if (prev_alloc == false || next_alloc == false) {
                printf(BOLD RED"Coalesce Invariant failed at line %d with heap:\n"RESET, line);
                print_heap();
                return false; // INVARIANT 1
            }
        }
    }

    // loop through the free list for all invariants requiring the free list
    block_t *f_block;
    for (f_block = free_list_head; f_block != NULL; f_block = f_block->next) {
        free_list_count++; // increment count of free list blocks

        // Check that the free list block is actually free
        if (get_alloc(f_block)) {
            printf(BOLD RED"Allocated Block in Free List Invariant Broken at line %d with heap:\n"RESET, line);
            print_heap();
            return false; // INVARIANT 2
        }

        // Check that the free list is doubly linked
        if (f_block->next != NULL && f_block->next->prev != f_block) {
            printf(BOLD RED"Free List Not Doubly Linked Invariant Broken at line %d with heap:\n"RESET, line);
            print_heap();
            return false; // INVARIANT 3
        }

        if(free_list_count > 1000000000) {
            printf(BOLD RED"Free List in an Infinite Loop at line %d with heap:\n"RESET, line);
            print_heap();
            return false; // INVARIANT 5
        }

    }



     // Check that the number of free blocks in the heap
     // is equal to the number of free blocks in the free list.
    if (free_list_count != heap_count) {
        printf(BOLD RED"Free List Has All Free Blocks Invariant failed at line %d with heap:\n"RESET, line);
        print_heap();
        return false; // INVARIANT 4
    }


    return true;
}

/**
 * @brief prints the heap
 *
 * @return true if printed successfully (allows for use inside of assert)
 *
 * @Changelog
 * - Created during Coalesce Phase for debugging use.
 */
bool print_heap() {
/*
 * Include color codes to copy over print heap for debugging student code.
 *
 * #define RED     "\033[0;31m"
 * #define BLUE    "\033[0;34m"
 * #define BOLD    "\033[1m"
 * #define RESET   "\033[0m"
 *
 */

    int count = 1;

    for (block_t * b = heap_start; get_size(b) != 0; b = find_next(b)) {
        bool alloc = get_alloc(b);

        char *alloc_status = alloc ? RED"ALLOC"RESET : BLUE"FREE"RESET;
        printf(BOLD"BLOCK %d"RESET" with ADDR: %p, \talloc: %s, \tsize: %lu",
               count, b, alloc_status, get_size(b));
        if (alloc) {
            printf("\n");
        }
        else {
    		printf(BLUE"\tprev: %p\tnext: %p\n"RESET, b->prev, b->next);
        }
        count++;
    }
    printf(BOLD"END HEAP\n\n"RESET);

    return true; // return true to allow for use in dbg macros
}