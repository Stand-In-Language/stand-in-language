#ifndef TEL_IC_H
#define TEL_IC_H

#include <stdint.h>

void tel_ic_reduce(uint32_t** m, uint32_t* t, uint32_t* c);
void tel_ic_stuck(uint32_t** m, uint32_t* t, uint32_t* c, uint32_t n, uint32_t k, uint32_t msg,
                  uint32_t r1, uint32_t r2, uint32_t e1, uint32_t e2, uint32_t e3);

#endif
