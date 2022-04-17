#ifndef PTENTRY_H
#define PTENTRY_H

#include "types.h" //for uint

struct pt_entry {
    uint pdx : 10; // page directory index of the virtual page
    uint ptx : 10; // page table index of the virtual page
    uint ppage : 20; // physical page number 
    uint present : 1; // 1 if page is present
    uint writable : 1; // 1 if page is writable
    uint user : 1;  // 1 if page belongs to user
    uint encrypted : 1; // 1 if page is currently encrypted
    uint ref : 1;  // For part A, set to 1. For part B, 1 if page is referenced until last time enqueued.
};

#endif