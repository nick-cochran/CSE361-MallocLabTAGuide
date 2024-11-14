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


/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

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


/**
 * @brief initialize the heap to be used by malloc
 *
 * @Changelog
 * - Provided Function at Init.
 */
bool mm_init(void) 
{
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
 * @brief
 *
 * @param size
 *
 * @return
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

/*
 * <what does coalesce do?>
 *
 * Changelog:
 * - Provided Function at Init.
 */
/**
 * @brief
 *
 * @param block
 *
 * @return
 *
 * @Changelog
 * - Provided Function at Init.
 */
static block_t *coalesce(block_t * block) 
{
    // fill me in
    return block;
}

/*
 * <what does place do?>
 *
 * Changelog:
 * - Provided Function at Init.
 */
/**
 * @brief
 *
 * @param block
 * @param asize
 *
 * @Changelog
 * - Provided Function at Init.
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);

    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;
        write_header(block, asize, true);
        write_footer(block, asize, true);

        block_next = find_next(block);
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);
    }

    else
    { 
        write_header(block, csize, true);
        write_footer(block, csize, true);
    }
}

/*
 * <what does find_fit do?>
 *
 * Changelog:
 * - Provided Function at Init.
 */
/**
 * @brief
 *
 * @param asize
 * @return
 *
 * @Changelog
 * - Provided Function at Init.
 */
static block_t *find_fit(size_t asize)
{
    block_t *block;

    for (block = heap_start; get_size(block) > 0;
                             block = find_next(block))
    {

        if (!(get_alloc(block)) && (asize <= get_size(block)))
        {
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
 * @return
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
 * @return
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
 * @return
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
 * @return
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
 * @return
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
 * @return
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
 * @param word
 *
 * @return
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
 * @return
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
 * @brief returns the next consecutive block on the heap by adding the
 *        size of the block.
 *
 * @param block
 *
 * @return
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
 * @return
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
 * @return
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
 * @brief given a payload pointer, returns a pointer to the
 *        corresponding block.
 *
 * @param bp
 *
 * @return
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
 * @return
 *
 * @Changelog
 * - Provided Function at Init.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}


/*
 * <what does your heap checker do?>
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)
{
    (void)line; // delete this line; it's a placeholder so that the compiler
                // will not warn you about an unused variable.
    return true;
}