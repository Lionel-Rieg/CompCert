#!/usr/bin/env sage
def mat_from_uint64(n):
  return Matrix(GF(2), [[(n >> (i*8+j)) & 1 for j in range(8)] for i in range(8)])

def uint64_from_mat(m):
  s = 0
  for i in range(8):
    for j in range(8):
      if m[i, j]:
        s += 1 << (i*8 + j)
  return s

matA=mat_from_uint64(0x12345678ABCDEF)
matB=mat_from_uint64(0x12345118ABCD32)

print hex(uint64_from_mat(matB * matA))
