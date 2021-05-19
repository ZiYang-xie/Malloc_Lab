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
#include <sys/mman.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ACode",
    /* First member's full name */
    "谢子飏",
    /* First member's email address */
    "19307130037@fudan.edu.cn",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static char *heap_listp;

/* ========================= Macros ========================= */

#define ALLOCATED 1
#define FREE 0

#define WSIZE 4 // 4bytes = 字
#define DSIZE 8 // 8bytes = 双字
#define CHUNKSIZE  (1<<12)  /* 初始化堆大小 */

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

/* 在 p 地址处读写一个字 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = val)

/* 获得 block 的 Size 或 Alloc 信息 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 获取 block 的 header 和 footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 获得给定block块的前驱或后继块 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* 获得当前\后继\前驱块大小 */
#define CRT_BLKSZ(bp) GET_SIZE(HDRP(bp))
#define NEXT_BLKSZ(bp) GET_SIZE(HDRP(NEXT_BLKP(bp)))
#define PREV_BLKSZ(bp) GET_SIZE(HDRP(PREV_BLKP(bp)))

/* ======================= Utils Define ========================= */

static void *extend_heap(size_t);
static void *coalesce(void *);
static size_t align_size(size_t);
static void *find_fit(size_t);
static void place(char *bp, size_t size);
static void deferred_coalesce();

/* ========================= Function ========================= */

/* 
 * //print_debug_info - go through the heap_list to print debug info
 */
static void print_debug_info(char* funcName)
{
    printf("\n----------------------------------------------------\n");
    printf("Function Name: %s\n", funcName);
    char *bp = heap_listp;
    while(GET_ALLOC(HDRP(bp)) != 1 || CRT_BLKSZ(bp) != 0){
        printf("块指针: %p \t 分配: %d \t 大小: %d\n", bp, GET_ALLOC(HDRP(bp)), CRT_BLKSZ(bp));
        bp = NEXT_BLKP(bp);
    }
    printf("块指针: %p \t 分配: %d \t 大小: %d\n", bp, GET_ALLOC(HDRP(bp)), CRT_BLKSZ(bp));
    printf("----------------------------------------------------\n\n");
}


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        // Alloc Error
        return -1; 
    PUT(heap_listp, 0);                                 /* 零扩展对齐 */
    PUT(heap_listp + WSIZE, PACK(DSIZE, ALLOCATED));    /* 起始块头部 */
    PUT(heap_listp + 2*WSIZE, PACK(DSIZE, ALLOCATED));  /* 起始块尾部 */
    PUT(heap_listp + 3*WSIZE, PACK(0, ALLOCATED));      /* 结尾块头部 */

    heap_listp += 2*WSIZE; // 对齐到起始块尾部

    /* 扩展空栈至 CHUNKSIZE bytes */
    if(extend_heap(CHUNKSIZE) == NULL)
        //Alloc Error
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize = align_size(size);    /* 调整后的块大小 */
    size_t extendsize;                  /* 扩展堆大小 */
    char *bp;

    /* Trivial Case */
    if(size == 0)
        return NULL;

    /* 寻找适配 */
    if((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    // /* 推迟合并后继续寻找 */
    // deferred_coalesce();

    // if((bp = find_fit(asize)) != NULL) {
    //     place(bp, asize);
    //     return bp;
    // }

    /* 未找到适配，分配更多堆空间 */
    extendsize = asize;
    //printf("In mm_malloc | size:%d -> asize: %d extendsize = %d\n\n", size, asize, extendsize);
    if((bp = extend_heap(extendsize)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block.
 */
void mm_free(void *ptr)
{
    char *bp = ptr;
    size_t size = CRT_BLKSZ(bp);

    PUT(HDRP(bp), PACK(size, FREE));
    PUT(FTRP(bp), PACK(size, FREE));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if(ptr == NULL)    
        return mm_malloc(size);
    else if(size == 0){
        mm_free(ptr);
        return NULL;
    }
    
    size_t asize = align_size(size), old_size = CRT_BLKSZ(ptr);
    char *oldptr = ptr;
    char *newptr;

    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(oldptr)));
    size_t total_size = CRT_BLKSZ(ptr);

    if(!next_alloc){
        total_size += NEXT_BLKSZ(ptr);
        PUT(HDRP(ptr), PACK(total_size, ALLOCATED));
        PUT(FTRP(ptr), PACK(total_size, ALLOCATED));
    }

    if(total_size == asize)
        return ptr;
    else if(total_size > asize){
        place(ptr, asize);
        return ptr;
    }
    else{
        newptr = mm_malloc(asize);
        if(newptr == NULL)
            return NULL;
        memcpy(newptr, ptr, MIN(old_size, size));
        mm_free(ptr);
        return newptr;
    }
    return NULL;
}

/* ========================= Utils ========================= */

/* 
 * extend_heap - 扩展堆，对齐words，并执行合并，返回bp指针
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    
    size = ALIGN(words);
    if((long)(bp = mem_sbrk(size)) == -1)
    {
        //printf("In Extend Heap | Alloc %d bytes failed\n", size);
        // Alloc Error
        return NULL;
    }
    
    /* 初始化空闲块的头尾和结尾块的头部 */
    PUT(HDRP(bp), PACK(size, FREE));                /* 空闲块头部 */
    PUT(FTRP(bp), PACK(size, FREE));                /* 空闲块尾部 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, ALLOCATED));   /* 结尾块头部 */
    
    //printf("In Extend Heap | Alloc %d bytes success // bp = %p\n", size, bp);
    //print_debug_info("extend_heap");
    // Coalesce 合并
    return coalesce(bp);
}

/* 
 * coalesce - 对bp指向块进行前后合并，返回bp指针
 */
static void *coalesce(void * bp)
{
    size_t prev_alloc =  GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc =  GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = CRT_BLKSZ(bp);

    if(prev_alloc && next_alloc){                   /* 前后非空闲 */
        //printf("In coalesce | coalesce failed 前后非空闲\n");
        //printf("目前 size: %d\n\n", size);
        return bp;
    }
    else if(prev_alloc && !next_alloc){             /* 后空闲 */
        //printf("In coalesce | coalesce success 后空闲\n");
        size += NEXT_BLKSZ(bp);
        PUT(HDRP(bp), PACK(size, FREE));
        PUT(FTRP(bp), PACK(size, FREE));
        //printf("合并至 size: %d\n\n", size);
    }
    else if(!prev_alloc && next_alloc) {            /* 前空闲 */
        size += PREV_BLKSZ(bp);
        PUT(FTRP(bp), PACK(size, FREE));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, FREE));
        bp = PREV_BLKP(bp);
        //printf("In coalesce | coalesce success 前空闲\n");
        //printf("合并至 size: %d // cur_alloc: %d // cur_size %d\n\n", size, GET_ALLOC(HDRP(bp)), CRT_BLKSZ(bp));
    }
    else {                                          /* 前后均空闲 */
        //printf("In coalesce | coalesce success 前后均空闲\n");
        size += NEXT_BLKSZ(bp) + PREV_BLKSZ(bp);
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, FREE));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, FREE));
        bp = PREV_BLKP(bp);
        //printf("合并至 size: %d\n\n", size);
    }
    return bp;
}

/* 
 * deferred_coalesce - 推迟合并
 */
static void deferred_coalesce()
{
    char *bp = heap_listp;
    while(CRT_BLKSZ(bp)){
        if(GET_ALLOC(HDRP(bp)) == 0)
            bp = coalesce(bp);
        bp = NEXT_BLKP(bp);
    }
}

/* 
 * align_size - 对块大小进行对齐，留出首尾空间，返回真实分配大小
 */
static size_t align_size(size_t size)
{
    /* 调整块大小 */
    if(size <= DSIZE)
        return 2*DSIZE;
    else 
        return DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    return 0;
}

/* 
 * find_fit - 寻找适配，返回适配到的空闲块指针
 */

/* First Fit */
static void *first_fit(size_t size)
{
    char *bp = heap_listp;
    size_t cur_alloc = GET_ALLOC(HDRP(bp));
    size_t cur_size = CRT_BLKSZ(bp);
    while(cur_size){
        if(!cur_alloc && cur_size >= size)
            return bp;
        bp = NEXT_BLKP(bp);
        cur_alloc = GET_ALLOC(HDRP(bp));
        cur_size = CRT_BLKSZ(bp);
    }
    return NULL;
}

/* Best Fit */
static void *best_fit(size_t size)
{
    char *bp = heap_listp;
    char *best = NULL;
    size_t cur_alloc = GET_ALLOC(HDRP(bp));
    size_t cur_size = CRT_BLKSZ(bp);
    size_t gap = cur_size - size;
    while(cur_size){
        if(!cur_alloc && cur_size >= size)
        {
            if(cur_size - size < gap)
            {
                gap = cur_size - size;
                best = bp;
            }
        }
        bp = NEXT_BLKP(bp);
        cur_alloc = GET_ALLOC(HDRP(bp));
        cur_size = CRT_BLKSZ(bp);
    }
    return cur_size > 0 ? best : NULL;
}

static void *find_fit(size_t size)
{
    return first_fit(size);
}

/* 
 * place - 分配块
 */

static void place(char *bp, size_t asize)
{
    //printf("In place | Alloc %d bytes successed // bp = %p\n\n", size, bp);
    size_t blk_size = CRT_BLKSZ(bp);
    size_t rm_size = blk_size - asize;
    
    if(rm_size > DSIZE){
        PUT(HDRP(bp), PACK(asize, ALLOCATED));
        PUT(FTRP(bp), PACK(asize, ALLOCATED));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(rm_size, FREE));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(rm_size, FREE));
    }
    else
    {
        PUT(HDRP(bp), PACK(blk_size, ALLOCATED));
        PUT(FTRP(bp), PACK(blk_size, ALLOCATED));
    }
    return;
}











