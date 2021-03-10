#include "sail.h"
#include "cheri_extras.h"
#include <stdio.h>

/* ***** Sail memory builtins ***** */

/*
 * We organise memory available to the sail model into a linked list
 * of dynamically allocated MASK + 1 size blocks.
 */
struct block {
  uint64_t block_id;
  uint8_t *mem;
  struct block *next;
};

static struct block *sail_tags = NULL;

/*
 * Must be one less than a power of two.
 */
static uint64_t MASK = 0xFFFFFFul;

unit write_tag_byte(const uint64_t address, const uint64_t tag_byte)
{
  uint64_t mask = address & ~MASK;
  uint64_t offset = address & MASK;

  struct block *current = sail_tags;

  while (current != NULL) {
    if (current->block_id == mask) {
      current->mem[offset] = (uint8_t) tag_byte;
      return UNIT;
    } else {
      current = current->next;
    }
  }

  /*
   * If we couldn't find a block matching the mask, allocate a new
   * one, write the byte, and put it at the front of the block list.
   */
  fprintf(stderr, "[Sail] Allocating new tag block 0x%" PRIx64 "\n", mask);
  struct block *new_block = malloc(sizeof(struct block));
  new_block->block_id = mask;
  new_block->mem = calloc(MASK + 1, sizeof(uint8_t));
  new_block->mem[offset] = (uint8_t) tag_byte;
  new_block->next = sail_tags;
  sail_tags = new_block;

  return UNIT;
}

uint64_t read_tag_byte(const uint64_t address)
{
  uint64_t mask = address & ~MASK;
  uint64_t offset = address & MASK;

  struct block *current = sail_tags;

  while (current != NULL) {
    if (current->block_id == mask) {
      return current->mem[offset];
    } else {
      current = current->next;
    }
  }

  return 0;
}
