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
    "",
    /* First member's email address */
    "",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

//#define DEBUG
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static char *heap_listp;
static char *global_list_start_ptr;

/* ========================= Macros ========================= */

#define ALLOCATED 1
#define FREE 0

#define WSIZE 4 // 4bytes = 字
#define DSIZE 8 // 8bytes = 双字
#define CHUNKSIZE  512  /* 初始化堆大小 */

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

/* 在 p 地址处读写一个字 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)val)

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

/* 块链表前驱后继 */
#define PRED(bp) ((char*)(bp) + WSIZE)
#define SUCC(bp) ((char*)bp)

/* 获取块链表前驱后继 */
#define PRED_BLKP(bp) (GET(PRED(bp)))
#define SUCC_BLKP(bp) (GET(SUCC(bp)))

/* 大小类总类数 */
// 从2^4,2^5....类推
#define SEG_LEN 15

/* ======================= Utils PreDefine ========================= */

static void Error_Handler(char *, char *);
static int get_index(size_t); 
static size_t align_size(size_t);

static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t, int);
static void *place(char *, size_t);

/* ========================= DEBUG ========================= */

/* print_funcname: 打印函数名 */
static void print_funcname(char *name) 
{
    printf("In %s\n", name);
}

/* print_heap_list: 打印堆块组织方式 */
static void print_heap_list(char* __FUNCNAME__)
{
    printf("-----------===  Block List ===--------------\n");
    print_funcname(__FUNCNAME__);
    char *bp = heap_listp;
    while(GET_ALLOC(HDRP(bp)) != 1 || CRT_BLKSZ(bp) != 0){
        if(!GET_ALLOC(HDRP(bp)) && !CRT_BLKSZ(bp)){
            Error_Handler(bp, "Heap Last Pointer Leak!!!\n");
            exit(-1);
        }
        printf("Block Pointer: %p \t Allocated: %d \t Size: %d\n", bp, GET_ALLOC(HDRP(bp)), CRT_BLKSZ(bp));
        bp = NEXT_BLKP(bp);
    }
    printf("Block Pointer: %p \t Allocated: %d \t Size: %d\n", bp, GET_ALLOC(HDRP(bp)), CRT_BLKSZ(bp));
    printf("----------------------------------------------------\n\n");
}

/* print_block_info: 打印bp指向块的详细信息 */
static void print_block_info(char* bp, char* __FUNCNAME__)
{
    printf("-------------=== BLOCK INFO ===----------------\n");
    print_funcname(__FUNCNAME__);
    printf("Pointer: %p\n", bp);
    char* __STATE__ = GET_ALLOC(HDRP(bp)) == ALLOCATED ? "ALLOCATED" : "FREE";
    printf("STATE: %s \t Header_SIZE: %d \t Footer_SIZE: %d\n", __STATE__, GET_SIZE(HDRP(bp)), GET_SIZE(FTRP(bp)));
    if(!GET_ALLOC(HDRP(bp))){
        int seg_index = get_index(CRT_BLKSZ(bp));
        char *root = global_list_start_ptr + seg_index * WSIZE;
        printf("ROOT: %p\n", root);
        if((void *)PRED_BLKP(bp)) printf("PRED_BLKP: %p \t", (void *)PRED_BLKP(bp)); else printf("PRED_BLKP: NULL \t");
        if((void *)SUCC_BLKP(bp)) printf("SUSUCC_BLKPC: %p \n", (void *)SUCC_BLKP(bp)); else printf("SUCC_BLKP: NULL \n");
    }
    
    printf("----------------------------------------------------\n\n");
}

/* print_free_list: 打印当前空闲列表信息 */
static void print_free_list(char* __FUNCNAME__)
{
    printf("-------------=== FREE BLOCK LIST ===----------------\n");
    print_funcname(__FUNCNAME__);
    int seg_idx = 0;

    while(seg_idx < SEG_LEN){
        char *root = global_list_start_ptr + seg_idx * WSIZE;
        char *bp = (char *)SUCC_BLKP(root);
        while(bp){
            char* __STATE__ = GET_ALLOC(HDRP(bp)) == ALLOCATED ? "ALLOCATED" : "FREE";
            printf("bp: %p \t ROOT: %p \t STATE: %s \t SIZE: %d \t", bp, root, __STATE__, CRT_BLKSZ(bp));
            
            if(!GET_ALLOC(HDRP(bp))){
                if((void *)PRED_BLKP(bp)) printf("PRED_BLKP: %p \t", (void *)PRED_BLKP(bp)); else printf("PRED_BLKP: NULL \t");
                if((void *)SUCC_BLKP(bp)) printf("SUSUCC_BLKPC: %p \n\n", (void *)SUCC_BLKP(bp)); else printf("SUCC_BLKP: NULL \n\n");
            }
            bp = (char *)SUCC_BLKP(bp);
        }
        seg_idx++;
    }

    printf("----------------------------------------------------\n\n");
}

/* show_free_link: 展示以root开头的大小类空闲链表 */
static void show_free_link(char* root)
{
    if(SUCC_BLKP(root))
        printf("ROOT: %p --> ", root);
    else {
        printf("ROOT: %p\n", root);
        return;
    }
    char *succ = (char *)SUCC_BLKP(root);
    while(SUCC_BLKP(succ)){
        printf("%p ---> ", succ);
        succ = (char *)SUCC_BLKP(succ);
    }
    printf("%p\n", succ);
}

/* Error_Handler: 打印错误信息 */
static void Error_Handler(char *bp, char *__ERROR_MSG__)
{
    printf("%s", __ERROR_MSG__);
    print_block_info(bp, "Error");
}

/* mm_check: 进行全局检查 */
static void mm_check() 
{
    char *cur_block;
    cur_block = heap_listp;

    // 直到结尾块结束
    while(CRT_BLKSZ(cur_block)) {
        // 检查头尾是否一致
        if(GET_SIZE(HDRP(cur_block)) != GET_SIZE(FTRP(cur_block)) || 
            GET_ALLOC(HDRP(cur_block)) != GET_ALLOC(FTRP(cur_block)))
            Error_Handler(cur_block, "Header and Footer Mismatch\n");
        // 检查合并
        if(!GET_ALLOC(HDRP(cur_block))) {
            if(!GET_ALLOC(PREV_BLKP(cur_block)))
                Error_Handler(cur_block, "PREV Coalescing Error\n");
            if(!GET_ALLOC(NEXT_BLKP(cur_block)))
                Error_Handler(cur_block, "NEXT Coalescing Error\n");
        }
        cur_block = NEXT_BLKP(cur_block);
    }

    // 检查是否有已分配的块在空闲块链表里
    int seg_idx;
    for(seg_idx = 0; seg_idx < SEG_LEN; seg_idx++) {
        cur_block = global_list_start_ptr + seg_idx * WSIZE;
        while(cur_block) {
            if(GET_ALLOC(HDRP(cur_block)))
                Error_Handler(cur_block, "Allocated Block in Free List\n");
            cur_block = (char *)SUCC_BLKP(cur_block);
        }
    }
}

/* ========================== LIST ========================== */

/* 
 * get_index - 由大小获得大小类序号
 */
static int get_index(size_t v) 
{
    // 本质上是位运算的 log 2, O(1)复杂度
    // 参考 'Bit twiddling hacks' by Sean Anderson 
    // Linking: https://graphics.stanford.edu/~seander/bithacks.html#IntegerLogLookup
    
    size_t r, shift;
    r = (v > 0xFFFF)   << 4; v >>= r;
    shift = (v > 0xFF) << 3; v >>= shift; r |= shift;
    shift = (v > 0xF)  << 2; v >>= shift; r |= shift;
    shift = (v > 0x3)  << 1; v >>= shift; r |= shift;
                                          r |= (v >> 1);
    // 从 2^4 开始 (空闲块最小 16 bytes)
    int x = (int)r - 4;
    if(x < 0) 
        x = 0;
    if(x >= SEG_LEN) 
        x = SEG_LEN - 1;
    return x;
}

/* 
 * insert_free_block - 插入块
 */
static void insert_free_block(char *fbp)
{
    // 获得插入块所属大小类
    int seg_index = get_index(CRT_BLKSZ(fbp));
    char *root = global_list_start_ptr + seg_index * WSIZE;

    #ifdef INDEBUG
        print_heap_list("Insert");
        printf("Inserting FreeBLock....\n");
        print_block_info(fbp,"Insert_free_block");
    #endif

    // 地址排序 - Address Order
    void *succ = root;
    
    while(SUCC_BLKP(succ)){
        succ = (char *)SUCC_BLKP(succ);
        if((unsigned int)succ >= (unsigned int)fbp){
            // 安装地址顺序插入空闲块
            // PRED_BLKP(succ) <-> fbp <-> succ
            char *tmp = succ;
            succ = (char *)PRED_BLKP(succ);
            PUT(SUCC(succ), fbp);
            PUT(PRED(fbp), succ);
            PUT(SUCC(fbp), tmp);
            PUT(PRED(tmp), fbp);
            #ifdef INDEBUG
                printf("succ(PRE): %p \t tmp(SUCC): %p \t", succ, tmp);
                print_free_list("Insert");
            #endif
            return;
        }
    }
    
    // Base Case & Last Case 
    // 当前大小类无空闲块 或者 在地址分配时当前空闲块地址最大被分配在最后
    PUT(SUCC(succ), fbp);
    PUT(PRED(fbp), succ);
    PUT(SUCC(fbp), NULL);
    #ifdef INDEBUG
        print_free_list("Insert");
    #endif
}

/* 
 * delete_free_block - 删除块
 */
static void delete_free_block(char *fbp)
{
    int seg_index = get_index(CRT_BLKSZ(fbp));
    char *root = global_list_start_ptr + seg_index * WSIZE;

    #ifdef DEBUG
        printf("Deleting....\n");
        print_block_info(fbp, "TOBE_DELETE_BLOCK");
        print_free_list("Del");

        // Check Del Free Block
        if(GET_ALLOC(HDRP(fbp))){
            Error_Handler(fbp, "Delete NOT FREE BLOCK!!!!\n");
            exit(-1);
        }

        // Check Del Root Block
        if(fbp == root){
            Error_Handler(fbp, "DEL Root Block!!\n");
            exit(-1);
        }
    #endif
    
    // NORMAL: GOT A SUCCESSOR AND PREDECESSOR
    if(SUCC_BLKP(fbp) && PRED_BLKP(fbp)){
        #ifdef DEBUG
            printf("Normal BP: %p\tRoot: %p\tSUCC_BLKP: %p\tPRED_BLKP: %p\n",
                fbp, root, SUCC_BLKP(fbp), PRED_BLKP(fbp));
        #endif
        PUT(SUCC(PRED_BLKP(fbp)), SUCC_BLKP(fbp));
        PUT(PRED(SUCC_BLKP(fbp)), PRED_BLKP(fbp));
    }
    else if(PRED_BLKP(fbp)){ // LAST BLOCK
        #ifdef DEBUG
            printf("Last BP: %p\tRoot: %p\tSUCC_BLKP: %p\tPRED_BLKP: %p\n",
                fbp, root, SUCC_BLKP(fbp), PRED_BLKP(fbp));
            if(PRED_BLKP(fbp) == root)
                printf("No Block Left\n");
        #endif
        PUT(SUCC(PRED_BLKP(fbp)), NULL);
    }

    PUT(SUCC(fbp), NULL);
    PUT(PRED(fbp), NULL);
}


/* ========================= FUNCTION ========================= */

/* 
 * mm_init - 初始化
 */
int mm_init(void)
{
    #ifdef DEBUG
        printf("MM_init\n");
    #endif

    if((heap_listp = mem_sbrk((SEG_LEN + 3) * WSIZE)) == (void *)-1)
        // 分配错误
        return -1;
    int i;

    /* 空闲块 */
    for(i = 0; i < SEG_LEN; ++i)
        PUT(heap_listp + i*WSIZE, NULL);	            // 初始化空闲块大小类头指针

    /* 分配块 */
    PUT(heap_listp + (i+0)*WSIZE, PACK(DSIZE, ALLOCATED));  /* 序言块头部 */
    PUT(heap_listp + (i+1)*WSIZE, PACK(DSIZE, ALLOCATED));  /* 序言块尾部 */
    PUT(heap_listp + (i+2)*WSIZE, PACK(0, ALLOCATED));      /* 结尾块头部 */

    global_list_start_ptr = heap_listp;
    heap_listp += (i+1)*WSIZE; // 对齐到起始块有效载荷

    /* 扩展空栈至 CHUNKSIZE bytes */
    if(extend_heap(CHUNKSIZE) == NULL)
        //Alloc Error
        return -1;
    return 0;
}

/* 
 * mm_malloc - 分配块，首次适配 & 立即合并策略
 */
void *mm_malloc(size_t size)
{
    #ifdef DEBUG
        printf("Mallocing.....\n");
    #endif
    size_t asize = align_size(size);    /* 调整后的块大小 */
    size_t extendsize;                  /* 扩展堆大小 */
    char *bp;

    /* Trivial Case */
    if(size == 0)
        return NULL;

    /* 寻找适配 */
    if((bp = find_fit(asize, get_index(asize))) != NULL)
        return place(bp, asize);

    /* 未找到适配，分配更多堆空间 */
    extendsize = MAX(asize, CHUNKSIZE);
    //printf("In mm_malloc | size:%d -> asize: %d extendsize = %d\n\n", size, asize, extendsize);
    if((bp = extend_heap(extendsize)) == NULL)
        return NULL;

    return place(bp, asize);
}

/*
 * mm_free - 释放块并立即合并
 */
void mm_free(void *ptr)
{
    #ifdef DEBUG
        printf("Freeing.....\n");
    #endif
    char *bp = ptr;
    size_t size = CRT_BLKSZ(bp);

    PUT(HDRP(bp), PACK(size, FREE));
    PUT(FTRP(bp), PACK(size, FREE));
    coalesce(bp);
}

/*
 * mm_realloc - 重新分配
 */
void *mm_realloc(void *ptr, size_t size)
{
    #ifdef REDEBUG
        print_heap_list("Realloc");
        print_block_info(ptr, "To Be Realloc Block");
        printf("Realloc Size； %d\n", size);
    #endif
    // 如果 ptr == NULL 直接分配
    if(ptr == NULL)    
        return mm_malloc(size);
    // 如果 size == 0 就释放
    else if(size == 0){
        mm_free(ptr);
        return NULL;
    }
    size_t asize = align_size(size), old_size = CRT_BLKSZ(ptr);
    size_t mv_size = MIN(asize, old_size);
    char *oldptr = ptr;
    char *newptr;

    if(old_size == asize)
        return ptr;
    
    size_t prev_alloc =  GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc =  GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t next_size = NEXT_BLKSZ(ptr);
    char *next_bp = NEXT_BLKP(ptr);
    size_t total_size = old_size;

    #ifdef REDEBUG
        printf("Old_size: %d \t Asize: %d \n", old_size, asize);
    #endif
    if(prev_alloc && !next_alloc && (old_size + next_size >= asize)){    // 后空闲  
        total_size += next_size;
        delete_free_block(next_bp);
        PUT(HDRP(ptr), PACK(total_size, ALLOCATED));
        PUT(FTRP(ptr), PACK(total_size, ALLOCATED));
        place(ptr, total_size);
    }
    else if(!next_size && asize >= old_size){
        size_t extend_size = asize - old_size;
        if((long)(mem_sbrk(extend_size)) == -1)
            return NULL; 
        
        PUT(HDRP(ptr), PACK(total_size + extend_size, ALLOCATED));
        PUT(FTRP(ptr), PACK(total_size + extend_size, ALLOCATED));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, ALLOCATED)); 
        place(ptr, asize);
    }
    else{
        newptr = mm_malloc(asize);
        if(newptr == NULL)
            return NULL;
        memcpy(newptr, ptr, MIN(old_size, size));
        mm_free(ptr);
        return newptr;
    }
    #ifdef REDEBUG
        // DEBUG FOOTER
        printf("------------------- End ------------------------\n");
    #endif
    return ptr;
}

/* ========================= Utils ========================= */

/* 
 * extend_heap - 扩展堆，对齐size，并执行合并，返回bp指针
 */
static void *extend_heap(size_t asize)
{
    #ifdef DEBUG
        printf("Extending Heap.....\n");
    #endif
    char *bp;

    if((long)(bp = mem_sbrk(asize)) == -1){
        // Alloc Error
        return NULL;
    }
    
    /* 初始化空闲块的头尾和结尾块的头部 */
    PUT(HDRP(bp), PACK(asize, FREE));                /* 空闲块头部 */
    PUT(FTRP(bp), PACK(asize, FREE));                /* 空闲块尾部 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, ALLOCATED));    /* 结尾块头部 */

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
        insert_free_block(bp);
        return bp;
    }
    else if(prev_alloc && !next_alloc){             /* 后空闲 */
        #ifdef DEBUG
            printf("Coalesce 后空闲\n");
            print_block_info(bp, "Coalesce");
        #endif
        size += NEXT_BLKSZ(bp);
        delete_free_block(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, FREE));
        PUT(FTRP(bp), PACK(size, FREE));
        PUT(PRED(bp), NULL);
        PUT(SUCC(bp), NULL);
    }
    else if(!prev_alloc && next_alloc) {            /* 前空闲 */
        #ifdef DEBUG
            print_heap_list("Coalesce 前空闲");
            print_block_info(bp, "Coalesce");
        #endif
        size += PREV_BLKSZ(bp);
        delete_free_block(PREV_BLKP(bp));

        PUT(FTRP(bp), PACK(size, FREE));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, FREE));

        bp = PREV_BLKP(bp);
        PUT(PRED(bp), NULL);
        PUT(SUCC(bp), NULL);
    }
    else {                                          /* 前后均空闲 */
        #ifdef DEBUG
            printf("Coalesce 前后均空闲\n");
            print_block_info(bp, "Coalesce");
        #endif
        size += NEXT_BLKSZ(bp) + PREV_BLKSZ(bp);
        delete_free_block(PREV_BLKP(bp));
        delete_free_block(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, FREE));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, FREE));
        bp = PREV_BLKP(bp);
        PUT(PRED(bp), NULL);
        PUT(SUCC(bp), NULL);
    }
    insert_free_block(bp);
    return bp;
}

/* 
 * align_size - 对块大小进行对齐，留出首尾空间，返回真实分配大小
 */
static size_t align_size(size_t size)
{
    /* 调整块大小 */
    if(size <= DSIZE) return 2*DSIZE;
    else return DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // Code Never Went Here
    return 0;
}

/* 
 * find_fit - 寻找适配，返回适配到的空闲块指针,使用首次适配
 */

static void *find_fit(size_t size, int seg_idx)
{
    // First Fit
    #ifdef DEBUG
        printf("Fitting.....\n");
    #endif
    char* res;
    while(seg_idx < SEG_LEN){
        char *root = global_list_start_ptr + seg_idx * WSIZE;
        char *bp = (char *)SUCC_BLKP(root);
        while(bp){
            if((size_t)CRT_BLKSZ(bp) >= size)
                return bp;
            
            bp = (char *)SUCC_BLKP(bp);
        }
        // 在这类中未找到适合，在更大类中寻找
        seg_idx++;
    }
    return NULL;
}

/* 
 * place - 放置块，若剩余后部大于一个最小块大小(16 bytes)就进行分割
 */
static void *place(char *bp, size_t asize)
{
    size_t blk_size = CRT_BLKSZ(bp);
    size_t rm_size = blk_size - asize;
    #ifdef DEBUG
        printf("Placing......\n");
        print_heap_list("Before Placeing");
    #endif

    if(!GET_ALLOC(HDRP(bp)))
        delete_free_block(bp);
    if(rm_size >= 2*DSIZE){
        if(asize > 64){
            PUT(HDRP(bp), PACK(rm_size, FREE));
            PUT(FTRP(bp), PACK(rm_size, FREE));
            PUT(HDRP(NEXT_BLKP(bp)), PACK(asize, ALLOCATED));
            PUT(FTRP(NEXT_BLKP(bp)), PACK(asize, ALLOCATED));
            insert_free_block(bp);
            return NEXT_BLKP(bp);
        }
        else{
            PUT(HDRP(bp), PACK(asize, ALLOCATED));
            PUT(FTRP(bp), PACK(asize, ALLOCATED));
            PUT(HDRP(NEXT_BLKP(bp)), PACK(rm_size, FREE));
            PUT(FTRP(NEXT_BLKP(bp)), PACK(rm_size, FREE));

            coalesce(NEXT_BLKP(bp));
        }
    }
    else{
        PUT(HDRP(bp), PACK(blk_size, ALLOCATED));
        PUT(FTRP(bp), PACK(blk_size, ALLOCATED));

        #ifdef DEBUG
            printf("Place Without Insert\n");
            print_heap_list("After Placing");
        #endif
    }
    return bp;
}











