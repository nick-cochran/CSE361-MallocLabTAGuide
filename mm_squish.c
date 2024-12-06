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
 *                                   Nth Fit                                  *
 *                               Remove Footers                               *
 *                              Segregated Lists                              *
 *                                                                            *
 *                               The Big Squish                               *
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
static const word_t prev_alloc_mask = 0x2;
static const word_t size_mask = ~(word_t)0xF;

static const int N = 75; // N for Nth fit -- best for seg lists seems to be ~75
static const size_t min_moe_size = 256;
static const size_t max_size = ~0x0;

static const int char_bits = 8; // 8 bits in 1 byte
static const int num_bits_word_t = sizeof(word_t) * char_bits; // number of bytes in word_t * 8 = number of bits
static const int log2_min_block_size = 4; // log2(16) = 4 --> min_block_size isn't 16 yet but will be soon
static const int last_list_index = 9;
static const int seg_list_count = 10;


typedef struct block
{
    // header: size + allocation flag + previous block allocation flag
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
// Segregated Free List Headers
static block_t *seg_lists[] = {NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL};
// Segregated Free List Min Sizes -- used only for printing/debugging
static const size_t seg_list_sizes[] = {16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192};


/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc, bool prev_alloc);

static size_t extract_size(word_t word);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t word);
static bool get_alloc(block_t *block);
static bool get_prev_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc, bool prev_alloc);
static void write_footer(block_t *block, size_t size, bool alloc, bool prev_alloc);
static void update_next_prev_alloc(block_t *block, bool prev_alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static void list_insert(block_t *block);
static void list_remove(block_t *block);

static int find_seg_list_index(size_t asize);

bool mm_checkheap(int lineno);
bool print_heap();
bool print_seg_lists();


/**
 * @brief initialize the heap to be used by malloc
 *
 * @Changelog
 * - Provided Function at Init.
 * - Added explicit free list head to NULL. (previous commit -- whoops)
 * - Added prev_alloc functionality for Remove Footers.
 * - Added Seg List Initialization.
 */
bool mm_init(void) 
{
    // set seg list heads to NULL for when the code resets
    for(int i = 0; i < seg_list_count; i++) {
        seg_lists[i] = NULL;
    }

    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true, true); // Prologue footer
    start[1] = pack(0, true, true); // Epilogue header
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
 * - Updated to utilize space with Remove Footers.
 */
void *malloc(size_t size) 
{
    dbg_printf(BOLD MAGENTA"MALLOC CALLED with size: %lu\n"RESET, size);
    dbg_ensures(print_heap());
    dbg_ensures(print_seg_lists());

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
    asize = round_up(size + wsize, dsize);
    // ensure that asize does not roundup to less than min_block_size
    if(asize < min_block_size) {
        asize = min_block_size;
    }

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
 * - Updated to work better with Remove Footers.
 */
void free(void *bp)
{
    dbg_printf(BOLD CYAN"FREE CALLED with addr: %p\n"RESET, bp);
    dbg_ensures(print_heap());
    dbg_ensures(print_seg_lists());

    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);

    update_next_prev_alloc(coalesce(block), false);

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
 * - Added prev_alloc functionality for Remove Footers.
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
    // use the fact that this is where the epilogue used to be to get the previous block's alloc status
    bool epilogue_prev_alloc = get_prev_alloc(block);
    write_header(block, size, false, epilogue_prev_alloc);
    write_footer(block, size, false, epilogue_prev_alloc);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true, false);

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
 * - Added prev_alloc functionality for Remove Footers.
 */
static block_t *coalesce(block_t * block) 
{
    block_t *next_block = find_next(block);

    size_t block_size = get_size(block);

     // check edge case where previous block is prologue
    bool prev_alloc = get_prev_alloc(block);
    bool next_alloc = get_alloc(next_block);

    // case 1
    if(prev_alloc && next_alloc) {
        write_header(block, block_size, false, prev_alloc);
        write_footer(block, block_size, false, prev_alloc);
        list_insert(block);
        return block;
    }

    size_t next_size = get_size(next_block);

    // case 2
    if(prev_alloc && !next_alloc) {
        block_size += next_size;
        list_remove(next_block);

        write_header(block, block_size, false, prev_alloc);
        write_footer(block, block_size, false, prev_alloc);

        list_insert(block);
        return block;
    }

    block_t *prev_block = find_prev(block);

     // note realized later -->
     // this can be set to true since it cannot be a free block before another free block
    bool prev_prev_alloc = true; // instead of: get_prev_alloc(prev_block);
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

    write_header(prev_block, block_size, false, prev_prev_alloc);
    write_footer(prev_block, block_size, false, prev_prev_alloc);

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
 * - Added prev_alloc functionality for Remove Footers.
 * - Slightly modified to work correctly with Segregated Lists.
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);
    bool prev_alloc = get_prev_alloc(block);

    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;
        list_remove(block);
        write_header(block, asize, true, prev_alloc);

        block_next = find_next(block);
        prev_alloc = true; // set prev_alloc to true since we just allocated the previous block
        write_header(block_next, csize-asize, false, prev_alloc);
        write_footer(block_next, csize-asize, false, prev_alloc);
        update_next_prev_alloc(block_next, false);
        list_insert(block_next);
    }
    else
    { 
        list_remove(block);
        write_header(block, csize, true, prev_alloc);
        update_next_prev_alloc(block, true);
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
 * - Changed to Nth fit algorithm with explicit free list.
 * - Changed to Nth fit with Segregated Free Lists.
 */
static block_t *find_fit(size_t asize)
{
    int list_index = find_seg_list_index(asize);

    const int moe_divider = 20;
    size_t perf_block_size;
    // create a margin of error of what the perfect block size is
    // In theory this would be an improvement, but in testing it's unclear
    // otherwise just have it check that block_size is == to asize and finish loop there
    if(asize >= min_moe_size) {
        perf_block_size = asize + round_up(asize/moe_divider, dsize);
    } else {
        perf_block_size = asize;
    }

    // set up vars for Nth fit
    int blocks_found = 0;
    block_t *best_block = NULL;
    size_t best_block_size = max_size; // set to max size (unsigned ~0x0) to compare with first

    int i = list_index;
    for(; i < seg_list_count; i++) { // loop through seg lists

        block_t *block = seg_lists[i];
        if(block == NULL) { // if seg list is empty, move to next list
            continue;
        }

        for(; block != NULL; block = block->next) { // loop through seg list

            size_t block_size = get_size(block);
            if(asize <= block_size) {
                blocks_found++;

                // check if block size is the best possible option and return immediately if so
                if(block_size <= perf_block_size) {
                    return block;
                }

                if(block_size < best_block_size) {
                    best_block = block;
                    best_block_size = block_size;
                }
            }

            // end the loop if we have found N blocks that fit
            if(blocks_found >= N) {
                return best_block;
            }
        }

        // if we have found something that fits, don't search the rest of the lists
        if(blocks_found > 0) {
            break;
        }
    }

    return best_block; // NULL if no block found
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
 * - Added prev_alloc parameter for Remove Footers.
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc)
{
    return alloc ? (prev_alloc ? (size | alloc_mask | prev_alloc_mask) : (size | alloc_mask))
                    : (prev_alloc ? (size | prev_alloc_mask) : size);
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
 * - Changed in remove footer. (added changelog in a later commit)
 */
static size_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
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
 * @brief returns the previous allocation status of a given block using it's header.
 *
 * @param block the block to get the prev_alloc bit from.
 *
 * @return true if the previous block is allocated, false otherwise.
 *
 * @Changelog
 * - Added function for Remove Footers.
 */
static bool get_prev_alloc(block_t *block)
{
    return (bool)(block->header & prev_alloc_mask);
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
 * - Added prev_alloc parameter for Remove Footers.
 */
static void write_header(block_t *block, size_t size, bool alloc, bool prev_alloc)
{
    block->header = pack(size, alloc, prev_alloc);
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
 * - Added prev_alloc parameter for Remove Footers.
 */
static void write_footer(block_t *block, size_t size, bool alloc, bool prev_alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc, prev_alloc);
}

/**
 * @brief given a block, updates the next block's previous allocation status
 *
 * @param block the block which has changed allocation status
 *
 * @Changelog
 * - Added Function for Remove Footers.
 */
static void update_next_prev_alloc(block_t *block, bool prev_alloc) {
    block_t *next_block = find_next(block);
    write_header(next_block, get_size(next_block), get_alloc(next_block), prev_alloc);
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
 * @brief insert the block at the beginning of the correct seg list
 *
 * @param block the block to be inserted
 *
 * @ChangeLog
 * - Added Function for Explicit Free List.
 * - Modified for Segregated Free Lists.
 */
static void list_insert(block_t *block) {

    int list_index = find_seg_list_index(get_size(block));
    block_t *list_head = seg_lists[list_index];

    // empty free list
    if(list_head == NULL) {
        block->prev = NULL;
        block->next = NULL;
    }
    // at least one item in the free list
    else {
        block->prev = NULL;
        block->next = list_head;
        list_head->prev = block;
    }
    seg_lists[list_index] = block;
}

/**
 * @brief remove the block from the correct seg list
 *
 * @param block the block to be removed
 *
 * @ChangeLog
 * - Added Function for Explicit Free List.
 * - Modified for Segregated Free Lists.
 */
static void list_remove(block_t *block) {

    int list_index = find_seg_list_index(get_size(block));

    block_t *prev_block = block->prev;
    block_t *next_block = block->next;

    if(prev_block == NULL && next_block == NULL) {
        seg_lists[list_index] = NULL;
    }
    else if(prev_block == NULL) {
        next_block->prev = NULL;
        seg_lists[list_index] = next_block;
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
 * @brief Uses __builtin_clzll to find the index of the seg list for a block of the given size.
 *
 * @param asize the size of the block going in the free lists
 *
 * @return the index of the correct seg list
 *
 * @credit
 * - Thanks to Andrew Carpenter for the idea and Eric Todd for additional ideas
 *
 * @Changelog
 * - Added for Segregated List Implementation.
 */
static int find_seg_list_index(size_t asize) {
    // returns the number of leading zeros in the binary representation of asize
    int leading_zeros = __builtin_clzll(asize);
    // convert to the number of trailing zeros with (num_bits_word_t - leading zeros - 1)
    int trailing_zeros = num_bits_word_t - leading_zeros - 1;
    int index = trailing_zeros - log2_min_block_size;  // subtract log2(min_block_size) to start at index 0
    if (index < 0) index = 0;
    // return the last index if it is larger than the corresponding size for that index
    return index <= last_list_index ? index : last_list_index;
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
 * - Added Remove Footers Invariants -- 6, 7.
 * - Added Segregated Free List Invariant -- 8.
 */
bool mm_checkheap(int line)
{

    int free_list_count = 0;
    int heap_count = 0;

    block_t *b;
    // loop through the heap for all invariants requiring the entire heap
    for (b = heap_start; get_size(b) != 0; b = find_next(b)) {
        block_t * next = find_next(b);

        bool b_alloc = get_alloc(b);
        bool prev_alloc = get_prev_alloc(b);
        bool next_alloc = get_alloc(next);

        if (b_alloc == false) {
            heap_count++; // increment count of free blocks in the heap

            // Check that Coalesce works as intended
            if (prev_alloc == false || next_alloc == false) {
                printf(BOLD RED"Coalesce Invariant failed at line %d with heap:\n"RESET, line);
                print_heap();
                return false; // INVARIANT 1
            }

            if (b->header != *find_prev_footer(next)) {
                printf(BOLD RED"Footer Not Matching Header Invariant Broken at line %d with heap:\n"RESET, line);
                print_heap();
                return false; // INVARIANT 6
            }
        }

        if(b_alloc != get_prev_alloc(next)) {
            printf(BOLD RED"Incorrect Prev Alloc Bit Invariant Broken at line %d with heap:\n"RESET, line);
            print_heap();
            return false; // INVARIANT 7
        }
    }

    // loop through the seg lists for all invariants requiring the seg free lists
    int list_index = 0;
    for(; list_index < seg_list_count; list_index++) {

        block_t *f_block = seg_lists[list_index];
        for(; f_block != NULL; f_block = f_block->next) {
            free_list_count++; // increment count of free list blocks
            size_t block_size = get_size(f_block);

            // Check that the free list block is actually free
            if(get_alloc(f_block)) {
                printf(BOLD RED"Allocated Block (addr: %p) in Seg List Invariant"
                               " Broken at line %d with heap:\n"RESET, f_block, line);
                print_heap();
                print_seg_lists();
                return false; // INVARIANT 2
            }

            // Check that the free list is doubly linked
            if(f_block->next != NULL && f_block->next->prev != f_block) {
                printf(BOLD RED"Seg List (index: %d) Not Doubly Linked Invariant"
                               " Broken at line %d with heap:\n"RESET, list_index, line);
                print_heap();
                return false; // INVARIANT 3
            }

            // Check that all blocks are in the correct Seg List
            if(block_size >= seg_list_sizes[list_index]
                && (list_index+1 == seg_list_count || block_size < seg_list_sizes[list_index+1])) {
                printf(BOLD RED"Block in Wrong Seg List Invariant Broken at line %d with heap:\n"RESET, line);
                print_heap();
                print_seg_lists();
                return false; // INVARIANT 8
            }

            const int too_large_number = 1000000000;
            if(free_list_count > too_large_number) {
                printf(BOLD RED"Free Lists in an Infinite Loop at line %d with heap:\n"RESET, line);
                print_heap();
                return false; // INVARIANT 5
            }

        }
    }



     // Check that the number of free blocks in the heap
     // is equal to the number of free blocks in the free list.
    if (free_list_count != heap_count) {
        printf(BOLD RED"Free Lists Doesn't Have All Free Blocks Invariant failed at line %d with heap:\n"RESET, line);
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
 * #define MAGENTA "\033[0;35m"
 * #define CYAN    "\033[0;36m"
 * #define BOLD    "\033[1m"
 * #define RESET   "\033[0m"
 *
 */

    int count = 1;

    for (block_t * b = heap_start; get_size(b) != 0; b = find_next(b)) {
        bool alloc = get_alloc(b);

        char *alloc_status = alloc ? RED"ALLOC"RESET : BLUE"FREE"RESET;
        char *prev_alloc_status = get_prev_alloc(b) ? MAGENTA"ALLOC"RESET : CYAN"FREE"RESET;
        printf(BOLD"BLOCK %d"RESET" with ADDR: %p, \talloc: %s, \tprev_alloc: %s, \tsize: %lu",
               count, b, alloc_status, prev_alloc_status, get_size(b));
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

/**
 * @brief prints the segregated free lists
 *
 * @return true to allow for use in dbg macros
 *
 * @Changelog
 * - Created for Seg Lists to debug and print the segregated free lists.
 */
bool print_seg_lists() {
/*
 * Include color codes to copy over print seg lists for debugging student code.
 *
 * #define RED     "\033[0;31m"
 * #define BLUE    "\033[0;34m"
 * #define MAGENTA "\033[0;35m"
 * #define CYAN    "\033[0;36m"
 * #define BOLD    "\033[1m"
 * #define RESET   "\033[0m"
 *
 */
    int list_index = 0;
    printf(BOLD"SEGREGATED FREE LISTS\n"RESET);
    printf(BOLD"------------------------------------------------------------\n"RESET);

    for(; list_index < seg_list_count; list_index++) {
        printf(BOLD BLUE"SEG LIST %d with min size: %lu\n"RESET, list_index, seg_list_sizes[list_index]);

        block_t *block = seg_lists[list_index];
        if(block == NULL) {
            printf(BOLD"Empty Seg List\n"RESET);
            continue;
        }
        int count = 1;
        for(; block != NULL; block = block->next, count++) {
            printf(BOLD"Block %d"RESET" with ADDR: %p, \tsize: %lu\n", count, block, get_size(block));
        }
    }
    printf(BOLD"------------------------------------------------------------\n\n"RESET);

    return true; // return true to allow for use in dbg macros
}