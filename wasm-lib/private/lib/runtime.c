#include <math.h>
#include <stdint.h>

int32_t iadd32(int32_t a, int32_t b) {
  return a + b;
}

int32_t isub32(int32_t a, int32_t b) {
  return a - b;
}

int32_t imul32(int32_t a, int32_t b) {
  return a * b;
}

uint32_t idiv32_u(uint32_t a, uint32_t b) {
  return a / b;
}

int32_t idiv32_s(int32_t a, int32_t b) {
  return a / b;
}

uint32_t irem32_u(uint32_t a, uint32_t b) {
  return a % b;
}

int32_t irem32_s(int32_t a, int32_t b) {
  return a % b;
}

int32_t iand32(int32_t a, int32_t b) {
  return a & b;
}

int32_t ior32(int32_t a, int32_t b) {
  return a | b;
}

int32_t ixor32(int32_t a, int32_t b) {
  return a ^ b;
}

int32_t ishl32(int32_t a, int32_t b) {
  return a << (b % 32);
}

uint32_t ishr32_u(uint32_t a, uint32_t b) {
  return a >> (b % 32);
}

int32_t ishr32_s(int32_t a, int32_t b) {
  return a >> (b % 32);
}

int32_t irotl32(uint32_t a, uint32_t b) {
#if defined(__clang__)
  return __builtin_rotateleft32(a, b % 32);
#else
  b = b % 32;
  return (a << b) | (a >> (-b & 31));
#endif
}

int32_t irotr32(uint32_t a, uint32_t b) {
#if defined(__clang__)
  return __builtin_rotateright32(a, b % 32);
#else
  b = b % 32;
  return (a >> b) | (a << (-b & 31));
#endif
}

int32_t ieqz32(int32_t a) {
  return a == 0 ? 1 : 0;
}

int32_t ieq32(int32_t a, int32_t b) {
  return a == b ? 1 : 0;
}

int32_t ine32(int32_t a, int32_t b) {
  return a != b ? 1 : 0;
}

int32_t ilt32_u(uint32_t a, uint32_t b) {
  return a < b ? 1 : 0;
}

int32_t ilt32_s(int32_t a, int32_t b) {
  return a < b ? 1 : 0;
}

int32_t igt32_u(uint32_t a, uint32_t b) {
  return a > b ? 1 : 0;
}

int32_t igt32_s(int32_t a, int32_t b) {
  return a > b ? 1 : 0;
}

int32_t ile32_u(uint32_t a, uint32_t b) {
  return a <= b ? 1 : 0;
}

int32_t ile32_s(int32_t a, int32_t b) {
  return a <= b ? 1 : 0;
}

int32_t ige32_u(uint32_t a, uint32_t b) {
  return a >= b ? 1 : 0;
}

int32_t ige32_s(int32_t a, int32_t b) {
  return a >= b ? 1 : 0;
}

int32_t iclz32(int32_t a) {
  return __builtin_clz(a);
}

int32_t ictz32(int32_t a) {
  return __builtin_ctz(a);
}

int32_t ipopcnt32(int32_t a) {
  return __builtin_popcount(a);
}

int32_t iwrap32(int64_t a) {
  return (int32_t)a;
}

uint32_t itrunc32_32_u(float a) {
  return (uint32_t)trunc(a);
}

int32_t itrunc32_32_s(float a) {
  return (int32_t)trunc(a);
}

uint32_t itrunc32_64_u(double a) {
  return (uint32_t)trunc(a);
}

int32_t itrunc32_64_s(double a) {
  return (int32_t)trunc(a);
}

int64_t iadd64(int64_t a, int64_t b) {
  return a + b;
}

int64_t isub64(int64_t a, int64_t b) {
  return a - b;
}

int64_t imul64(int64_t a, int64_t b) {
  return a * b;
}

uint64_t idiv64_u(uint64_t a, uint64_t b) {
  return a / b;
}

int64_t idiv64_s(int64_t a, int64_t b) {
  return a / b;
}

uint64_t irem64_u(uint64_t a, uint64_t b) {
  return a % b;
}

int64_t irem64_s(int64_t a, int64_t b) {
  return a % b;
}

int64_t iand64(int64_t a, int64_t b) {
  return a & b;
}

int64_t ior64(int64_t a, int64_t b) {
  return a | b;
}

int64_t ixor64(int64_t a, int64_t b) {
  return a ^ b;
}

int64_t ishl64(int64_t a, int64_t b) {
  return a << (b % 64);
}

uint64_t ishr64_u(uint64_t a, uint64_t b) {
  return a >> (b % 64);
}

int64_t ishr64_s(int64_t a, int64_t b) {
  return a >> (b % 64);
}

int64_t irotl64(uint64_t a, uint64_t b) {
#if defined(__clang__)
  return __builtin_rotateleft64(a, b % 64);
#else
  b = b % 64;
  return (a << b) | (a >> (-b & 63));
#endif
}

int64_t irotr64(uint64_t a, uint64_t b) {
#if defined(__clang__)
  return __builtin_rotateright64(a, b % 64);
#else
  b = b % 64;
  return (a >> b) | (a << (-b & 63));
#endif
}

int64_t ieqz64(int64_t a) {
  return a == 0 ? 1 : 0;
}

int64_t ieq64(int64_t a, int64_t b) {
  return a == b ? 1 : 0;
}

int64_t ine64(int64_t a, int64_t b) {
  return a != b ? 1 : 0;
}

int64_t ilt64_u(uint64_t a, uint64_t b) {
  return a < b ? 1 : 0;
}

int64_t ilt64_s(int64_t a, int64_t b) {
  return a < b ? 1 : 0;
}

int64_t igt64_u(uint64_t a, uint64_t b) {
  return a > b ? 1 : 0;
}

int64_t igt64_s(int64_t a, int64_t b) {
  return a > b ? 1 : 0;
}

int64_t ile64_u(uint64_t a, uint64_t b) {
  return a <= b ? 1 : 0;
}

int64_t ile64_s(int64_t a, int64_t b) {
  return a <= b ? 1 : 0;
}

int64_t ige64_u(uint64_t a, uint64_t b) {
  return a >= b ? 1 : 0;
}

int64_t ige64_s(int64_t a, int64_t b) {
  return a >= b ? 1 : 0;
}

int64_t iclz64(int64_t a) {
  return __builtin_clz(a);
}

int64_t ictz64(int64_t a) {
  return __builtin_ctz(a);
}

int64_t ipopcnt64(int64_t a) {
  return __builtin_popcount(a);
}

int64_t iextend32_u(uint32_t a) {
  return (int64_t)a;
}

int64_t iextend32_s(int32_t a) {
  return (int64_t)a;
}

uint64_t itrunc64_32_u(float a) {
  return (uint64_t)trunc(a);
}

int64_t itrunc64_32_s(float a) {
  return (int64_t)trunc(a);
}

uint64_t itrunc64_64_u(double a) {
  return (uint64_t)trunc(a);
}

int64_t itrunc64_64_s(double a) {
  return (int64_t)trunc(a);
}

float fabs32(float a) {
  return fabsf(a);
}

float fneg32(float a) {
  return -a;
}

float fceil32(float a) {
  return ceilf(a);
}

float ffloor32(float a) {
  return floorf(a);
}

float ftrunc32(float a) {
  return truncf(a);
}

float fnearest32(float a) {
  return roundf(a);
}

float fsqrt32(float a) {
  return sqrtf(a);
}

float fadd32(float a, float b) {
  return a + b;
}

float fsub32(float a, float b) {
  return a - b;
}

float fmul32(float a, float b) {
  return a * b;
}

float fdiv32(float a, float b) {
  return a / b;
}

float fmin32(float a, float b) {
  return fminf(a, b);
}

float fmax32(float a, float b) {
  return fmaxf(a, b);
}

float fcopysign32(float a, float b) {
  return copysignf(a, b);
}

int64_t feq32(float a, float b) {
  return a == b ? 1 : 0;
}

int64_t fne32(float a, float b) {
  return a != b ? 1 : 0;
}

int64_t flt32(float a, float b) {
  return a < b ? 1 : 0;
}

int64_t fgt32(float a, float b) {
  return a > b ? 1 : 0;
}

int64_t fle32(float a, float b) {
  return a <= b ? 1 : 0;
}

int64_t fge32(float a, float b) {
  return a >= b ? 1 : 0;
}

float fdemote64(double a) {
  return (float)a;
}

double fabs64(double a) {
  return fabs(a);
}

double fneg64(double a) {
  return -a;
}

double fceil64(double a) {
  return ceil(a);
}

double ffloor64(double a) {
  return floor(a);
}

double ftrunc64(double a) {
  return trunc(a);
}

double fnearest64(double a) {
  return round(a);
}

double fsqrt64(double a) {
  return sqrt(a);
}

double fadd64(double a, double b) {
  return a + b;
}

double fsub64(double a, double b) {
  return a - b;
}

double fmul64(double a, double b) {
  return a * b;
}

double fdiv64(double a, double b) {
  return a / b;
}

double fmin64(double a, double b) {
  return fmin(a, b);
}

double fmax64(double a, double b) {
  return fmax(a, b);
}

double fcopysign64(double a, double b) {
  return copysign(a, b);
}

int64_t feq64(double a, double b) {
  return a == b ? 1 : 0;
}

int64_t fne64(double a, double b) {
  return a != b ? 1 : 0;
}

int64_t flt64(double a, double b) {
  return a < b ? 1 : 0;
}

int64_t fgt64(double a, double b) {
  return a > b ? 1 : 0;
}

int64_t fle64(double a, double b) {
  return a <= b ? 1 : 0;
}

int64_t fge64(double a, double b) {
  return a >= b ? 1 : 0;
}

double fpromote32(float a) {
  return (double)a;
}

double fconvert64_u(uint64_t a) {
  return (double)a;
}

double fconvert64_s(int64_t a) {
  return (double)a;
}
