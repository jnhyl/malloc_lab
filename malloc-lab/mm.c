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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // 0x7 == 0b111, 즉 & ~0x7은 하위 3비트를 0으로 만듦 -> 0b1000, 8의 배수 만족

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))     // size_t: unsigned long int, 크기 : (64bit machine) 8bytes, (32bits machine) 4bytes

// ----------------------------------------------------------------------------------------------------------------------------------------------------
// 함수 선언
int mm_init(void);
void mm_free(void *bp);
void *mm_malloc(size_t size);
void *mm_realloc(void *ptr, size_t size);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

// -----------------------------------------------------------------------------------------------------------------------------------------------------
/* 가용 리스트 조작을 위한 기본 상수 및 매크로 정의 */
/* 기본 상수와 매크로 */
#define WSIZE       4       /* 1 word = 4 bytes, header와 footer 사이즈*/
#define DSIZE       8       /* double words = ALIGNMENT = 8 bytes*/
#define CHUNKSIZE   (1<<12) /* 힙 확장 시 기준 크기, 4kb로 확장*/

#define MAX(x, y)   ((x) > (y) ? (x) : (y)) /*x와 y 중 더 큰 값 반환*/

/* 크기와 할당 비트를 하나의 워드로 포장 */
#define PACK(size, alloc)   ((size) | (alloc))  /* 더블 워드 정렬 조건 때문에 size는 항상 8의 배수, 하위 비트 3개는 항상 0이다.*/

/* 주소 p에서 워드 읽기/쓰기 */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p의 헤더/푸터에서 크기와 할당 비트 추출 */
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x7)

/* 블록 포인터(실제 페이로드가 담기는 주소 시작 위치)bp의 헤더와 푸터의 주소 계산*/
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) /*블록 사이즈에는 헤더와 푸터 크기 포함, 페이로드의 크기 = 블록 사이즈 - 헤더와 푸터의 크기 합*/

/* 블록 포인터 bp의 다음/이전 블록 포인터 계산*/
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))   /* 현재 블록의 헤더(bp - WSIZE)에서 GET_SEZE */
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))   /* 이전 블록의 푸터(bp - DSIZE)에서 GET_SIZE */

// -----------------------------------------------------------------------------------------------------------------------------------------------------

/*  mm_init - 할당기 사용 전 초기화
    사용할 힙 할당, 힙의 최대 크기는 MAX_HEAP (20*(1<<20)), 20MB
    prologue block 생성 : 실제 블록처럼, double word alignment 지킴, header와 footer로 이루어짐
    eplogue block 생성 : size가 0인 header 하나로 구성, 하위 비트는 allocated, 1로 되어있다.
*/

/* 정적 전역변수 heap_listp 선언, 항상 prologue block을 가리키는 포인터(사실상 푸터의 주소를 가리킴)*/
static char *heap_listp;

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)     // 할당기 초기화를 위해서 힙 공간에 4 words 공간 할당
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    // 프롤로그 블록 헤더
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    // 프롤로그 블록 푸터
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        // 에필로그 블록
    heap_listp += (2*WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)       // 할당에 사용할 빈 힙 확장, word 갯수를 인자로 받는다.
        return -1;

    return 0;
}

/*
 * extend_heap - 사용할 힙 공간 확장, 헬퍼 함수
 */
static void *extend_heap(size_t words)  // bytes가 아닌 words 단위로 인자를 받음, ex) CHUNKSIZE/WSIZE
{
    char *bp;       // 할당할 주소, 페이로드의 주소
    size_t size;    // 할당할 힙 공간 사이즈, 더블 워드 정렬 조건 지킴, mem_sbrk 함수 인자로 쓰이기 위해 words 단위를 bytes로 변형

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;   // 더블 워드 조건에 맞게 사이즈 조정
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));           /* free block header*/
    PUT(FTRP(bp), PACK(size, 0));           /* free block footer*/
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header*/

    return coalesce(bp);
}

/*
 * coalesce - 가용 블록 연결 함수, csapp 묵시적 할당기는 즉시 연결 방식
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case 1, 다음/이전 블록이 모두 할당된 상태
    if (prev_alloc && next_alloc) {
        return bp;
    }

    // case 2, 다음 블록만 가용 상태
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3, 이전 블록만 가용 상태
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // case 4, 다음/이전 블록 모두 가용 상태
    else {
        size += GET_SIZE(FTRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

// -----------------------------------------------------------------------------------------------------------------------------------------

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // 실제 필요한 공간 : 할당하고 싶은 공간 + 헤더와 푸터의 공간 + (패딩, ALIGNMENT 조건 만족)
    // ALIGN(size + header_size + footer_size) == ALIGN(size + WSIZE + WSIZE)
    // = ALIGN(size + SIZE_T_SIZE)
    size_t asize = ALIGN(size + SIZE_T_SIZE);   // Adjusted block size
    size_t extendsize;      // 확장 필요 시 확장할 힙 공간
    char *bp;               // block pointer

    // Ignore spurious requests
    if (size == 0)
        return NULL;

    // Search the free list for a fit
    if ((bp = find_fit(asize)) != NULL) {   // 현재 할당된 힙 공간에 적당한 가용 공간이 있으면
        place(bp, asize);
        return bp;
    }

    // No fit found. Get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);     // 확장할 힙 크기 결정, asize의 크기가 작으면 미리 정해 둔 CHUNKSIZE 사용
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)   // 확장 실패 시 NULL 반환
        return NULL;
    place(bp, asize);   // 확장 성공 시 extend_heap 함수는 coalesce 후 연결된 블록의 bp를 반환, 해당 주소를 bp로 갖는 공간에 asize 크기의 할당된 블록 생성
    return bp;
}

/*
 * find_fit : malloc, realloc 시 적당한 크기(= asize)의 가용 블록을 찾는 함수
 * 할당 가능한 가용 블록을 찾으면 해당 블록의 페이로드 주소를 반환
 * first fit으로 구현 - csapp p829 9.9.12장의 연습문제 9.8 참고
 */
static void *find_fit(size_t asize)
{
    char *bp = NEXT_BLKP(heap_listp);

    // while 문의 조건을 'GET(HDRP(bp)) != 1'로 해도 통과하긴 하나
    // 정석적인 방식은 GET_SIZE(HDRP(bp)) != 0
    // epilogue 블록은 size = 0, allocated bit = 1 (물론 실제 size != 0)
    // PACK(0, 1)을 이용하면 header에는 1이 저장된다.
    // 즉, 에필로그 블록의 header 정보를 확인하는가, 아님 거기서 size를 확인하는가 차이인데
    // 개인적으로 뭔 차이가 있나 싶지만 전자의 경우 할당 오류가 생길 수도 있다고 한다 (chatgpt 피셜)
    // 정석을 따르자
    while (GET_SIZE(HDRP(bp)) != 0) {
        if (GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) >= asize)
            return bp;
        bp = NEXT_BLKP(bp);
    }

    // find_fit 함수를 처음 짰을 때는 자꾸 이미 할당된 공간에 중복 할당이 발생한다는 에러 문구가 반복적으로 떴다.
    // 이유를 알아보니 공간의 크기(asize와 같거나 큰 공간)만 고려했지 가용, 할당 여부는 확인을 안 했다;;
    // 당연하게도 가용 블록만 할당 가능, 이미 할당된 블록에는 추가로 할당하면 안 된다.(할당기 법칙 위배됨)
    // GET_ALLOC(HDRP(bp)) == 0 <- 반드시 필요한 조건이니 꼭 기억하자

    return NULL;    // fit한 공간 없음, extend_heap 필요
}

/*
 * place : find_fit으로 찾은 가용 블록에 할당된 블록 생성
 */
static void place(void *bp, size_t asize)
{
    size_t rest_size = GET_SIZE(HDRP(bp));

    // 해당 가용 블록의 크기가 asize와 딱 맞게 fit 하면 상관이 없지만
    // 만일 asize 보다 클 경우 해당 블록 전체를 할당할지 분할할지 고려해야 한다.
    
    // 나의 경우 처음에 해당 블록의 크기가 asize의 크기보다 조금이라도 크다면 분할하도록 구현했다.
    // 어차피 코드 블록 전체가 double word align 정책에 맞게 크기가 규격화가 되어있기 때문에
    // 만일 공간이 남아도 0 아니면 DSIZE의 배수가 된다.
    // 즉 header + footer로만 이루어진 최소 크기의 블록이 가능하기에 문제 없다고 판단
    // rest - asize != 0 이면 무조건 분할하도록 했다.

    // 그러나 chatgpt피셜 더블 워드 정렬 조건에 안 맞는, 더 작은 공간이 생길 수도 있고
    // header와 footer로만 이루어진 가용 블록은 할당이 불가능한 무의미한 공간이기 때문에
    // rest - asize >= 2 * DSIZE, (header + payload + footer, 더블 워드 정책 만족)의 조건식을 추천
    // 또한 교재의 연습문제 9.9의 place 구현 문제에 따르면 
    // 나머지 부분의 크기가 최소 블록 크기와 같거나 큰 겨우에만 분할해야 한다고 설명하고 있는데
    // 최소 블록의 크기 또한 교재의 연습문제의 조건을 참고하면
    // payload의 데이터가 최소한 1 byte보다 커야한다고 한다.
    // 즉, header와 footer의 크기 합인 DSIZE에 최소 1byte 이상의 페이로드와 doble word align 규칙을 적용하면
    // 최소 블록의 크기는 2 * DSIZE여야 한다.

    if ((rest_size - asize) >= 2*DSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(rest_size - asize, 0));
        PUT(FTRP(next_bp), PACK(rest_size - asize, 0));
    } else {
        PUT(HDRP(bp), PACK(rest_size, 1));
        PUT(FTRP(bp), PACK(rest_size, 1));
    }
}

// -------------------------------------------------------------------------------------------------------------------------------------------------------

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)                 // 헤더와 푸터의 하위 3비트, allocated 관련 비트를 1에서 0, free로 바꾼다.
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));      // 할당된 블록의 헤더의 allocated bit를 0으로 바꾼다.
    PUT(FTRP(ptr), PACK(size, 0));      // 할당된 블록의 푸터의 allocated bit를 0으로 바꾼다.
    coalesce(ptr);      // 즉시 연결, 이전과 다음 블록이 가용 상태면 연결해준다.
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    // 0) ptr과 size가 각각 NULL이거나 0일 경우 realloc 동작, malloc_lab.pdf 참고
    // if ptr is NULL, the call is equivalent to mm malloc(size);
    if (ptr == NULL) {
        return malloc(size);
    }

    // if size is equal to zero, the call is equivalent to mm free(ptr);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    // 재조정할 사이즈의 실제 필요 사이즈(payload + header + footer + padding(for align))
    size_t asize = ALIGN(size + DSIZE);

    // 1) 만약 재조정할 size가 기존 크기보다 같거나 작으면
    // size_t cur_size = GET_SIZE(HDRP(ptr)) - DSIZE;
    // if (size == cur_size) {
    //     return ptr;
    // } else if (size < cur_size) { 
    //     place(ptr, asize);

    //     if (GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0) {
    //         coalesce(NEXT_BLKP(ptr));
    //     }

    //     return ptr;
    // }

    // size가 기존 크기보다 작을 경우, 만약 제자리에서 크기를 줄여주면
    // 속도는 다소 빨라지는 느낌인데 메모리 효율은 엄청 나빠진다. 거의 반토막 수준;;
    // 그래서 일단 보류하겠다. (같을 경우는 상관 없음, 근데 그닥 성능 향상이 없어서 얘도 보류)

    // 2) 다음 블록이 가용 블록이고 두 블록의 사이즈 합이 asize보다 같거나 크면
    if (GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0) {
        size_t total_size = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))); 
        if (total_size >= asize) {
            // 현재 블록과 다음 블록을 합쳐서 가용 블록으로 만든다.
            PUT(HDRP(ptr), PACK(total_size, 0));
            PUT(FTRP(ptr), PACK(total_size, 0));

            // 두 블록이 합쳐져서 생긴 공간에 asize 크기의 공간을 할당, 같은 시작 위치이므로 내용을 복사할 필요는 없다.
            place(ptr, asize);
            return ptr;
        }
    }

    // 3) 2번 조건을 불만족 할 경우, 새 위치에 할당하고 내용 복사, 기존 포인터 해제(free)
    newptr = mm_malloc(size);

    if (newptr == NULL)
        return NULL;

    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);    // 기존 코드
    // 근데.. 헤더의 크기는 4, SIZE_T_SIZE는 8인데 이게 맞나?
    // 뭣보다 header 안 정보는 단순 블록의 size가 아니라 PACK(size, allocated bit)인데?;;
    // 더욱이 우리가 memcopy하고 싶은 부분은 payload 부분이지 블록 전체가 아니잖아?
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;  // 새 블록에 memcpy할 사이즈 범위(= payload 범위)
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;  // if ptr is not NULL, it must have been returned by an earlier call to mm malloc or mm realloc.
}

// • mm realloc: The mm realloc routine returns a pointer to an allocated region of at least size bytes with the following constraints.

// – if ptr is NULL, the call is equivalent to mm malloc(size);
// – if size is equal to zero, the call is equivalent to mm free(ptr);
// – if ptr is not NULL, it must have been returned by an earlier call to mm malloc or mm realloc.

// The call to mm realloc changes the size of the memory block pointed to by ptr (the old block) to size bytes and returns the address of the new block. Notice that the address of the new block might be the same as the old block, or it might be different, depending on your implementation, the amount of internal fragmentation in the old block, and the size of the realloc request.

// The contents of the new block are the same as those of the old ptr block, up to the minimum of the old and new sizes. Everything else is uninitialized. For example, if the old block is 8 bytes and the new block is 12 bytes, then the first 8 bytes of the new block are identical to the first 8 bytes of the old block and the last 4 bytes are uninitialized. Similarly, if the old block is 8 bytes and the new block is 4 bytes, then the contents of the new block are identical to the first 4 bytes of the old block.
