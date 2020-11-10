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
  return a << b;
}

uint32_t ishr32_u(uint32_t a, uint32_t b) {
  return a >> b;
}

int32_t ishr32_s(int32_t a, int32_t b) {
  return a >> b;
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

int32_t iwrap32(int64_t a) {
  return (int32_t)a;
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
  return a << b;
}

uint64_t ishr64_u(uint64_t a, uint64_t b) {
  return a >> b;
}

int64_t ishr64_s(int64_t a, int64_t b) {
  return a >> b;
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

uint64_t itrunc64_u(double a) {
  return (uint64_t)trunc(a);
}

int64_t itrunc64_s(double a) {
  return (int64_t)trunc(a);
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
