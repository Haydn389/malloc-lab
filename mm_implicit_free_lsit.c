/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "SW_Jungle week06-team-4",
    /* First member's full name */
    "euikyun choi",
    /* First member's email address */
    "ekchoi0502@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*macros*/
#define WSIZE 4             // word and header/footer size(bytes)
#define DSIZE 8             // double word size(bytes)
#define CHUNKSIZE (1 << 12) // heap 확장 : 4096 byte

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 최댓값 구하기

/*header에 들어가는 값(size and allocated bit)를 한 워드로*/
// #define PACK (size, alloc) ((size) | (alloc))
#define PACK(size, alloc) ((size) | (alloc))

/*p가 가리키는 워드 읽어오기, p가 가리키는 워드에 값 넣기*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/*header 에서 size field, allocated field 읽어오기*/
#define GET_SIZE(p) (GET(p) & ~0x7) //블럭크기 읽어오기
#define GET_ALLOC(p) (GET(p) & 0x1) //해당 블럭의 할당여부 읽어오기 1 : allocated, 0:free

/*블록 header 와 footer를 가리키는 포인터 return*/
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*다음과 이전블록의 블록포인터 리턴*/
#define NEXT_BLKP(bp) (((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) (((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)))

static void *heap_listp; // heap공간 첫 주소를 가리키는 정적 전역 변수 설정
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t a_size);
static void place(void *bp, size_t a_size);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);
    
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        return bp;
    }

    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size)
{
    size_t a_size;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;
    if (size <= DSIZE)
        a_size = 2 * DSIZE;
    else
    {
        a_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = find_fit(a_size)) != NULL)
    {
        place(bp, a_size);
        return bp;
    }

    extendsize = MAX(a_size, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, a_size);
    return bp;

    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
    //     return NULL;
    // else
    // {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
}

static void *find_fit(size_t a_size)
{
    void *bp;
    for (bp = (char *)heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (a_size <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t a_size)
{
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize - a_size) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(a_size, 1));
        PUT(FTRP(bp), PACK(a_size, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - a_size, 0));
        PUT(FTRP(bp), PACK(csize - a_size, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    // if (bp == NULL)
    //     return;
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldptr = bp;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
