/* The generated C emulator is missing this function.
   Up to this point, only used by --disable-compressed/-C.
   Make a dummy implementation of it.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

struct zMisa;

typedef int unit;
typedef uint64_t mach_bits;

unit z_set_Misa_C(struct zMisa * isa, mach_bits bits) {
    fprintf(stderr, "z_set_Misa_C is not supported\n");
    exit(EXIT_FAILURE);
}
