/*In this project, I use explicit free list appoach 
 *I delcear a linked list that link all the free block 
 *this linked list follow the FILO policy, the first node is the last free block 
 *for the find fit block function, I used first find approach
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Your UID */
    "UID: 404950730",
    /* Your full name */
    "Zhiheng Ma",
    /* Your email address */
    "ma.zhiheng@yahoo.com",
    /* Leave blank */
    "",
    /* Leave blank */
    ""
};

/* Basic constants and macros: */
#define WSIZE       4/* Word and header/footer size (bytes) */
#define DSIZE       8
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//access the next block
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
//access the previous or next node in the linked list
#define NEXT_PTR(p)  (*(char **)(p + WSIZE))
#define PREV_PTR(p)  (*(char **)(p))

/* Global variables: */
static char* free_list=0;
static char *heap_listp=0;

//helper function 
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static int coalesce_helper(size_t prev, size_t next);
static void set_node(void* ptr, int option);
// checker function
static void mm_checker(void ); 
static void block_check(void *bp);

/*initialize the memory
 * not parameter pass in
 * return 1 as sucessfull return -1 if fail
 * */
int mm_init(void)
{
	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(8 * WSIZE)) == NULL)
		return (-1);
	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);

	free_list=heap_listp;
       //extend the empty heap with a free block
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
	return (0);
}
/* input: seize of memory need to allocate
 * effect: allocate a playload with the size byte, 
 * playload has header and footer that indicate whether is used and the size of it
 * return an pointer to that block and Null for otherwise*/
void *mm_malloc(size_t size)
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;
       //Ignore the spurious requests
	if (size == 0)
		return (NULL);

       //adjust block size to include overhead
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

       //search free list
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

        //no fit found. ger more memory
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
		return (NULL);
	place(bp, asize);
	return (bp);
}
/*effect: free the specfic block
 * input: the pointer to that block*/
void mm_free(void *bp)
{
	size_t size;

	if (bp == NULL)
	   return;
    //free and coalesce the block
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*input: pointer to the block need to reallocate and the size 
 * effects: 1. if size is zero, free the specfic block
 *          2.if the block already is the least size of playload return ptr
 *          3.if the size in the current block is smaller than request size and the next block is free, sum the size
 *          4. if above conditions cannot satisfy allocate an new block and overwrite the old one*/
void *mm_realloc(void *ptr, size_t size)
{
	size_t old_size,new_size;
	void *newptr;

	//If size is negative it means nothing, just return NULL
	if((int)size < 0)
    	return NULL;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	if (ptr == NULL)
		return (mm_malloc(size));

	old_size=GET_SIZE(HDRP(ptr));
	new_size = size + (2 * WSIZE);
       //new size is smaller than the old one
	if (new_size <= old_size){
		return ptr;
	}
       //new size is greater than the old one
	else{
		size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
		size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
		size_t free_size = old_size + next_size;


		if(!next_alloc && free_size>= new_size){
			set_node(NEXT_BLKP(ptr),2);
			PUT(HDRP(ptr),PACK(free_size,1));
			PUT(FTRP(ptr),PACK(free_size,1));
			return ptr;
		}

		else{
			newptr=mm_malloc(new_size);

			if (newptr == NULL)
				return (NULL);

			place(newptr,new_size);
			memcpy(newptr,ptr,old_size);
			mm_free(ptr);
			return newptr;
		}
	}
}
/*effects: boundry coalescing
 *         Remove or insert the node to the explicit list
 *         return the coalescing pointer*/
static void *coalesce(void *bp)
{
   size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp ;
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
    int checker = coalesce_helper(prev_alloc,next_alloc);
   // checker equal 1 if previous and next block is not free
   //         euqal 2 if next is free
   //         equal 3 if previous is free
   //         default is for all other case
    switch(checker){

    case 1:{
		set_node(bp,1);
		return (bp);
	}

    case 2:{
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		set_node(NEXT_BLKP(bp),2);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
        break;
	}

     case 3:{
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		set_node(PREV_BLKP(bp),2);
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		break;
	}
                                             
    default:{
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		set_node(PREV_BLKP(bp),2);
		set_node(NEXT_BLKP(bp),2);
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		break;
	 }
        }
	set_node(bp,1);
	return (bp);
}

/*effect: extend an free block return the address*/
static void *extend_heap(size_t words)
{
	void *bp;
	size_t size;
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

	if ((bp = mem_sbrk(size)) == (void *)-1)
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	return (coalesce(bp));
}
static int coalesce_helper(size_t prev, size_t next)
{
    if (prev && next)
        return 1;

    else if (prev && !next)
        return 2;

    else if (!prev && next)
        return 3;

    else
        return 4;
}
/*input: the size of the block
 * effects: find the first free block in the explicit list
 *          Follow the find first approach
 *          return the first fit free block address
 */
static void *find_fit(size_t asize)
{
void *bp = free_list;

 while (GET_ALLOC(HDRP(bp))==0){

    if(GET_SIZE(HDRP(bp)) >= asize)
       return bp;

    bp = NEXT_PTR(bp);
  }
   return NULL;
}

/*effects: place an block of asize at the start of the free block bp
 *         split the block if the remain block is the minmum block size
 */
static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));
        size_t remain = csize - asize;

	if ((csize - asize) >= (2 * DSIZE)) {
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		set_node(bp,2);

		PUT(HDRP( NEXT_BLKP(bp)), PACK(remain, 0));
		PUT(FTRP( NEXT_BLKP(bp)), PACK(remain, 0));
		coalesce( NEXT_BLKP(bp));
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		set_node(bp,2);
	}
}
/* effects: modify the linked list
 *     option 1: insert an node to the linked list
 *     option 2: erase an node in the linked list
 *     explict free list
 */
static void set_node(void* ptr, int option) {
    
	switch (option) {
	case 1: {
		NEXT_PTR(ptr) = free_list;
		PREV_PTR(free_list) = ptr;
		PREV_PTR(ptr) = NULL;
		free_list = ptr;
		break;
	 }
	case 2: {
		if (PREV_PTR(ptr) != NULL)
			NEXT_PTR(PREV_PTR(ptr)) = NEXT_PTR(ptr);
		else
			free_list = NEXT_PTR(ptr);
		PREV_PTR(NEXT_PTR(ptr)) = PREV_PTR(ptr);
		break;
	  }
	}
}
// effects: perform to check the heap for consistency
static void mm_checker(void){
    void *bp = heap_listp; 

   if(GET_SIZE(HDRP(heap_listp)) != DSIZE || !GET_ALLOC(HDRP(heap_listp)))
      printf("Bad Prologue Header\n");
       

   while( GET_SIZE(HDRP(bp)) > 0) {
    block_check(bp);
    bp = (void *) NEXT_BLKP(bp);
   }

   if(GET_SIZE(HDRP(bp))!=0 || !GET_ALLOC(HDRP(bp)))
     printf("Bad Epilogue header\n");
}

//input: address of the block 
//effect: check the block whether aligned and footer and footer are match
static void block_check(void* bp){
    if ((unsigned int) bp % DSIZE) 
      printf("Error! Pointer: %p is not aligned\n", bp); 

   if(GET(HDRP(bp)) != GET(FTRP(bp)))
      printf ("Error! header not matching with footer\n");
}
