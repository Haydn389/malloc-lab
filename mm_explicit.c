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

// /* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8
// /* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*macros*/
#define WSIZE 4                           // word and header/footer size(bytes)
#define DSIZE 8                           // double word size(bytes)
#define CHUNKSIZE (1 << 12)               // heap 확장 : 4096 byte
#define MINIMUM 16                        // hd+pred+succ+footer=16byte
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
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*다음과 이전블록의 블록포인터 리턴*/
#define NEXT_BLKP(bp) (((char *)(bp) + GET_SIZE((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) (((char *)(bp)-GET_SIZE((char *)(bp)-DSIZE)))

/*free block 반환*/
#define SUCC_P(bp) (*(char **)(bp + WSIZE)) //(bp+WSIZE)가 가리키는 포인터(successor)반환 ,주소 값이 아닌 pointer 를 반환해주기 위해 이중포인터로 casting
#define PRED_P(bp) (*(char **)(bp))         // bp가 가리키는 포인터 (predecessor)반환


static char *heap_listp; // heap공간 첫 주소를 가리키는 정적 전역 변수 설정
static char *free_listp; // free_list의 맨 첫 블록을 가리키는 포인터
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t a_size);
static void place(void *bp, size_t a_size);
static void remove_block(void *bp);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                              /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(MINIMUM, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), 0);                /* pred */
    PUT(heap_listp + (3 * WSIZE), 0);                /* suc */
    PUT(heap_listp + (4 * WSIZE), PACK(MINIMUM, 1)); /* 블록의 footer */
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));       /* Epilogue header */
    heap_listp += (2 * WSIZE);
    free_listp = heap_listp;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size; // byte 단위

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if (size < MINIMUM) // size < 16byte 면 최소블럭사이즈로 맞춰주기
        size = MINIMUM;

    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // new epilogue header

    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    //앞뒤 모두 가용
    if (!prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_block(PREV_BLKP(bp));
        remove_block(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    //뒤 블럭만 가용
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_block(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    //앞 블럭만 가용
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        remove_block(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    //앞뒤 모두 할당된 경우
    // SUCC_P(bp) = free_listp; // bp의 succesor를 가리키는 포인터를 기존 첫 블럭 포인터 대입
    // PRED_P(bp) = NULL;       // bp의 pred를 NULL로 초기화
    // PRED_P(free_listp) = bp; // 기존 첫블럭의 pred를 bp로 업데이트
    // free_listp = bp;         // free_listp를

    *(char**)(bp+4) = free_listp; // bp의 succesor를 가리키는 포인터를 기존 첫 블럭 포인터 대입
    *(char**)(bp) = NULL;       // bp의 pred를 NULL로 초기화
    *(char**)(free_listp) = bp; // 기존 첫블럭의 pred를 bp로 업데이트
    free_listp = bp;         // free_listp를
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
    // fit 찾아 할당하기
    if ((bp = find_fit(a_size)) != NULL)
    {
        place(bp, a_size);
        return bp;
    }
    // fit이 없다면 메모리 get 후 place
    extendsize = MAX(a_size, CHUNKSIZE);
    //
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, a_size);
    return bp;
}

static void *find_fit(size_t a_size)
{

    char *bp;
    // succ po
    for (bp = free_listp; GET_ALLOC(HDRP(bp))!=1; bp = SUCC_P(bp))
    {
        if (a_size <= GET_SIZE(HDRP(bp)))
            return bp;
    }

    return NULL;
}

static void place(void *bp, size_t a_size)
{
    size_t csize = GET_SIZE(HDRP(bp));
    //전체 공간 중 필요공간을 뺀 나머지가 최소가용블록 이상일때
    if ((csize - a_size) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(a_size, 1));
        PUT(FTRP(bp), PACK(a_size, 1));
        remove_block(bp);   //할당 했으므로 list에서 제거
        //block 분할
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - a_size, 0));
        PUT(FTRP(bp), PACK(csize - a_size, 0));
        coalesce(bp);   //새 가용블록 연결
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_block(bp);
    }
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void remove_block(void *bp)
{
    // bp의 pred가 null이 아니면(즉 첫번째 블럭이 아니면)
    if (PRED_P(bp))
    {
        SUCC_P(PRED_P(bp)) = SUCC_P(bp); // bp의 pred의 succ에 bp의 succ 대입
        PRED_P(SUCC_P(bp)) = PRED_P(bp); // bp의 succ의 pred에 bp의 pred 대입
    }
    // bp의 pred가 null이면(첫번째 블럭이면)
    else
    {
        free_listp = SUCC_P(bp);         // free_listp가 bp의 successor 를가리키도록
        PRED_P(SUCC_P(bp)) = PRED_P(bp); // bp의 succ의 pred에 bp의 pred 대입
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */

// 방법2)
void *mm_realloc(void *bp, size_t size)
{
    if (size < 0)
        return NULL;
    else if (size == 0)
    {
        mm_free(bp);
        return NULL;
    }
    else
    {
        size_t old_size = GET_SIZE(HDRP(bp));
        size_t new_size = size + (2 * WSIZE); // 2 words(hd+ft)

        // new_size가 old_size보다 작거나 같으면 기존 bp 그대로 사용
        if (new_size <= old_size)
        {
            return bp;
        }
        // new_size가 old_size보다 크면 사이즈 변경
        else
        {
            size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
            size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));

            // next block이 가용상태이고 old, next block의 사이즈 합이 new_size보다 크면 그냥 그거 바로 합쳐서 쓰기
            if (!next_alloc && current_size >= new_size)
            {  
                remove_block(NEXT_BLKP(bp)); 
                PUT(HDRP(bp), PACK(current_size, 1));
                PUT(FTRP(bp), PACK(current_size, 1));
                return bp;
            }
            // 아니면 새로 block 만들어서 거기로 옮기기
            else
            {
                void *new_bp = mm_malloc(new_size);
                place(new_bp, new_size);
                memcpy(new_bp, bp, new_size); // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 new_size만큼의 문자를 new_bp로 복사해라!)
                mm_free(bp);
                return new_bp;
            }
        }
    }
}
