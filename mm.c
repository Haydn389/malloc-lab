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
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// Basic constants and macros
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)
#define INITCHUNKSIZE (1<<6)    // 64
#define LISTLIMIT 20
#define REALLOC_BUFFER (1<<7)   // 128

// calculate max value
#define MAX(x,y) ((x)>(y) ? (x) : (y))

//size와 할당 여부를 하나로 합친다
#define PACK(size,alloc) ((size)|(alloc))

//포인터 p가 가리키는 주소의 값을 가져온다.
#define GET(p) (*(unsigned int *)(p))

//포인터 p가 가리키는 곳에 val을 역참조로 갱신
#define PUT(p,val) (*(unsigned int *)(p)=(val))

//포인터 p가 가리키는 곳의 값에서 하위 3비트를 제거하여 블럭 사이즈를 반환(헤더+푸터+페이로드+패딩)
#define GET_SIZE(p) (GET(p) & ~0X7)
//포인터 p가 가리키는 곳의 값에서 맨 아래 비트를 반환하여 할당상태 판별
#define GET_ALLOC(p) (GET(p) & 0X1)

//블럭포인터를 통해 헤더 포인터,푸터 포인터 계산
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//블럭포인터 -> 블럭포인터 - WSIZE : 헤더위치 -> GET_SIZE으로 현재 블럭사이즈계산 -> 다음 블럭포인터 반환
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
//블럭포인터 -> 블럭포인터 - DSIZE : 이전 블럭 푸터 -> GET_SIZE으로 이전 블럭사이즈계산 -> 이전 블럭포인터 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//포인터 p가 가리키는 메모리에 포인터 bp을 입력
#define SET_bp(p, bp) (*(unsigned int *)(p) = (unsigned int)(bp))

//segregated list 내에서 next 와 prev의 포인터를 반환
#define SUCC(bp) (*(char **)(bp))
#define PRED(bp) (*(char **)(bp+WSIZE))

//전역변수 
char *heap_listp = 0;
void *segregated_free_lists[LISTLIMIT];

//함수 목록
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_node(void *bp, size_t size);
static void remove_block(void *bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int list;
    
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }
    
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    
    if (extend_heap(INITCHUNKSIZE/WSIZE) == NULL)
        return -1;  
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 요청받은 크기를 2워드 배수(8byte)로 반올림. 그리고 힙 공간 요청
    size = (words % 2) ? (words +1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));

    return coalesce(bp);        // 가용 블록 합치기
}

static void insert_node(void *bp, size_t size) 
{
    int idx = 0;   // 리스트의 인덱스
    void *search_bp = NULL; 
    void *insert_bp = NULL; //실제 노드가 삽입되는 위치
    
    // Select segregated list 
    // 2의 지수승으로 인덱스를 나누어 리스트를 관리하므로
    // size의 비트를 하나씩 제거하며 카운트를 세면 그 카운트수가 리스트의 index가 됨.
    while ((idx < LISTLIMIT - 1) && (size > 1)) 
    {
        size >>= 1;
        idx++;
    }
    
    // Keep size ascending order and search
    search_bp = segregated_free_lists[idx]; //search 시작할 주소 받기, 첫번째 insert라면 search_bp은 NULL
    // 오름차순으로 저장하기 위해 나보다 작은 놈들은 넘기고 나보다 큰놈 앞에서 멈추게 됨
    // search_bp가 null이 아니고(마지막 블럭 다음) size가 작은동안
    while ((search_bp != NULL) && (size > GET_SIZE(HDRP(search_bp)))) 
    {
        insert_bp = search_bp;        // insert bp에 기존에 있던 주소값으로 업데이트
        search_bp = SUCC(search_bp);  // search bp의 위치를 뒤 블록으로 옮김
    }
    // while문 돌고나면 삽입할 위치의 앞 블럭은 insert가, 뒷블럭은 search가 가리킴

    if (search_bp != NULL) //뒤 블럭이 NULL이 아니라면(=마지막 블럭이 아니라면)
    {   
        if (insert_bp != NULL) //앞 블럭도 NULL이 아니라면
        {   //case-1) 중간블럭
            SUCC(bp)=search_bp;               
            PRED(bp)=insert_bp; 
            PRED(search_bp)=bp;       
            SUCC(insert_bp)=bp;           
        } 
        else 
        {   //case-2) 맨 처음 블럭
            SUCC(bp)=search_bp;              
            PRED(bp)=NULL; 
            PRED(search_bp)=bp;
            segregated_free_lists[idx] = bp;    
        }
    } 
    else //뒤 블럭이 NULL이라면(=마지막 블럭이라면)
    {
        if (insert_bp != NULL) //앞 블럭이 NULL이 아니라면
        {   //case-3) 마지막 블럭
            SUCC(bp)=NULL;
            PRED(bp)=insert_bp;
            SUCC(insert_bp)=bp;
        } 
        else 
        {   //case-4) 처음이자 마지막 블럭
            SUCC(bp)=NULL;
            PRED(bp)=NULL;
            segregated_free_lists[idx] = bp;
        }
    }
    return;
}

static void remove_block(void *bp) 
{
    int idx = 0;
    size_t size = GET_SIZE(HDRP(bp));
    
    // Select segregated list 
    // 사이즈에 맞는 가용 리스트의 인덱스 찾기 (ex 2^12 -> 12)
    while ((idx < LISTLIMIT - 1) && (size > 1)) 
    {
        size >>= 1;
        idx++;
    }
    
    if (SUCC(bp) != NULL) 
    {   //bp가 마지막 블럭이 아니면
        if (PRED(bp) != NULL) 
        {   // pred 블록이 NULL이 아니면 (중간에 있는걸 지우는 경우)
            PRED(SUCC(bp))=PRED(bp);
            SUCC(PRED(bp))=SUCC(bp);

        } 
        else 
        {   // pred 블록이 NULL일 경우 (list에서 맨 처음을 지우는 경우)
            PRED(SUCC(bp))=NULL;// 뒷 블록의 앞 주소를 null로 변경
            segregated_free_lists[idx] = SUCC(bp);
        }
    } 
    else 
    {   //bp가 마지막 블럭이면
        if (PRED(bp) != NULL) 
        {   //리스트의 끝의 블록을 지우는 경우
            SUCC(PRED(bp))=NULL;
        } 
        else 
        {   // 애초에 하나만 존재했을 경우
            segregated_free_lists[idx] = NULL;
        }
    }
    
    return;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{

    size_t asize;
    size_t extendsize; //들어갈 자리가 없을때 늘려야 하는 힙의 용량
    
    char *bp;

    /* Ignore spurious*/
    if (size == 0)
        return NULL;
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp; 
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}


//전,후에 free block 이 있을시 합쳐줌 + 합쳐지는 경우 segregation_lists에서 기존 free block 노드 삭제해줌
// 합칠 때 기존 가용 블록들을 리스트에서 삭제하고 합쳐진 크기로 다시 리스트에 삽입
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc)
    {    // 뒷 블록이 가용 블록인 경우
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_block(NEXT_BLKP(bp));    // free list에서 bp 뒷 블록 삭제
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }
    else if (!prev_alloc && next_alloc)
    {    // 앞 블록이 가용 블록인 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        remove_block(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && !next_alloc)
    {               // 앞 뒷 블록이 모두 가용 블록인 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_block(PREV_BLKP(bp));
        remove_block(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }
    //앞뒤 모두 할당된 경우에는 그냥바로 insert (+그외 경우를 위한 insert)
    insert_node(bp,size);       // bp가 가용 블록의 위치이므로 가용 블록 추가
    return bp;
}

static void *find_fit(size_t asize)
{
    char *bp; 
    
    int idx = 0; 
    size_t searchsize = asize;      // 찾고자 하는 사이즈
    // Search for free block in segregated list
    // 인덱스 0부터 가용 리스트 검색, LIMIT(20)이상이면 종료
    while (idx < LISTLIMIT) 
    {
        // 적절한 idx를 찾기위해 searchsize를 계속 줄여 1이 되면 if문 진입
        // or (asize가 너무커서) 줄여나가다가 아직 1이 안됐음에도 idx가 이미 LIMIT에 도달한경우(2^20승이상) if문 진입
        if ((searchsize <= 1)||(idx == LISTLIMIT - 1)) 
        {
            bp = segregated_free_lists[idx];   // bp에 현재 search중인 블록 주소 넣기
            // bp 가 NULL 이거나 해당 size class 내에서 적당한 블럭 찾을때 까지 bp이동
            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp)))))  // bp 블록이 비어있지 않고 타겟사이즈를 넣을 수 있는 블록을 찾을 때까지
            {
                bp = SUCC(bp);  // 블록 탐색
            }
            if (bp != NULL)     // 할당 가능한 블록을 찾은 경우
                return bp;
        }
        
        searchsize >>= 1;   // 반복문 종료 조건
        idx++;              // 인덱스를 올려서 더 큰 블록을 서치
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    remove_block(bp);

    if ((csize-asize)>=(2*DSIZE))
    {
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp),PACK(csize-asize,0));
        PUT(FTRP(bp),PACK(csize-asize,0));
        coalesce(bp); // 이때 연결되어 있는 게 있을 수 있으므로 coalesce진행
    }
    else
    {
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    

    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// void *mm_realloc(void *bp, size_t size)
// {
//     void *oldbp = bp;
//     void *newbp;
//     size_t copySize;
    
//     newbp = mm_malloc(size);
//     if (newbp == NULL)
//       return NULL;
//     copySize = GET_SIZE(HDRP(oldbp));
//     if (size < copySize)
//       copySize = size;
//     memcpy(newbp, oldbp, copySize);
//     mm_free(oldbp);
//     return newbp;
// }

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
                void *new_bp = mm_malloc(new_size+128);//128
                // place(new_bp, new_size);
                memcpy(new_bp, bp, new_size); // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 new_size만큼의 문자를 new_bp로 복사해라!)
                mm_free(bp);
                return new_bp;
            }
        }
    }
}