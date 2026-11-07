#include <stdint.h>
#include <stddef.h>

#define TYPE int8_t
#define SIZE 9
#define OFFSET 0
#define AXIS0 3
#define AXIS1 3
#define STRIDE0 3
#define STRIDE1 1

void iterate(TYPE buffer[SIZE])
{
  size_t acc = OFFSET;
  size_t backstride1 = (AXIS1 - 1) * STRIDE1;

  for (int i = 0; i < AXIS0; i++)
  {
    for(int j = 0; j < AXIS1; j++)
    {
      buffer[acc];
      acc += STRIDE1;
    }
    acc += -backstride1 + STRIDE0;
  }
}
