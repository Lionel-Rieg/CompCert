#include "xor_and.h"

#define ADD ^=
#define MUL &

void xor_and_mat_mul1(unsigned m, unsigned n, unsigned p,
		     xor_and * restrict c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      c[i*stride_c+k] = 0;
    }
  }
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      for(unsigned j=0; j<n; j++) {
	c[i*stride_c+k] ADD (a[i*stride_a+j] MUL b[j*stride_b+k]); 
      }
    }
  }
}

void xor_and_mat_mul2(unsigned m, unsigned n, unsigned p,
		     xor_and * restrict c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      xor_and total = 0;
      for(unsigned j=0; j<n; j++) {
	total ADD (a[i*stride_a + j] MUL b[j*stride_b + k]);
      }
      c[i*stride_c+k] = total;
    }
  }
}

void xor_and_mat_mul3(unsigned m, unsigned n, unsigned p,
		     xor_and * restrict c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      xor_and total0 = 0, total1 = 0;
      unsigned j;
      for(j=0; j+1<n; j+=2) {
	total0 ADD (a[i*stride_a + j] MUL b[j*stride_b + k]);
	total1 ADD (a[i*stride_a + (j+1)] MUL b[(j+1)*stride_b + k]);
      }
      if (j < n) {
	total0 ADD a[i*stride_a + j] MUL b[j*stride_b + k];
      }
      total0 ADD total1;
      c[i*stride_c+k] = total0;
    }
  }
}

void xor_and_mat_mul4(unsigned m, unsigned n, unsigned p,
		     xor_and * c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b) {
  const xor_and *pa_i = a;
  xor_and * pc_i = c;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const xor_and *pb_j_k = b+k, *pa_i_j = pa_i;
      xor_and total = 0;
      for(unsigned j=0; j<n; j++) {
	total ADD (*pa_i_j MUL *pb_j_k);
	pa_i_j ++;
	pb_j_k += stride_b;
      }
      pc_i[k] = total;
    }
    pa_i += stride_a;
    pc_i += stride_c;
  }
}

void xor_and_mat_mul5(unsigned m, unsigned n, unsigned p,
		     xor_and * c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b) {
  const xor_and *pa_i = a;
  xor_and * pc_i = c;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const xor_and *pb_j_k = b+k, *pa_i_j = pa_i;
      xor_and total = 0;
      for(unsigned j2=0, n2=n/2; j2<n2; j2++) {
	xor_and p0 = *pa_i_j MUL *pb_j_k;
	pa_i_j ++;
	pb_j_k += stride_b;
	xor_and p1 = *pa_i_j MUL *pb_j_k;
	pa_i_j ++;
	pb_j_k += stride_b;
	total ADD p0;
	total ADD p1;
      }
      if (n%2) {
	total ADD *pa_i_j MUL *pb_j_k;
      }
      pc_i[k] = total;
    }
    pa_i += stride_a;
    pc_i += stride_c;
  }
}

#define CHUNK \
	    total ADD (*pa_i_j MUL *pb_j_k); \
	    pa_i_j ++; \
	    pb_j_k += stride_b;

void xor_and_mat_mul6(unsigned m, unsigned n, unsigned p,
		     xor_and * c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b) {
  const xor_and *pa_i = a;
  xor_and * pc_i = c;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const xor_and *pb_j_k = b+k, *pa_i_j = pa_i;
      xor_and total = 0;
      unsigned j2=0, n2=n/2;
      if (n2 > 0) {
	do {
	  CHUNK
	  CHUNK
	  j2++;
	} while (j2 < n2);
      }
      if (n%2) {
	total ADD (*pa_i_j MUL *pb_j_k);
      }
      pc_i[k] = total;
    }
    pa_i += stride_a;
    pc_i += stride_c;
  }
}

#define UNROLL 4
void xor_and_mat_mul7(unsigned m, unsigned n, unsigned p,
		     xor_and * c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b) {
  const xor_and *pa_i = a;
  xor_and * pc_i = c;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const xor_and *pb_j_k = b+k, *pa_i_j = pa_i;
      xor_and total = 0;
      {
	unsigned j4=0, n4=n/UNROLL;
	if (n4 > 0) {
	  do {
            CHUNK
	    CHUNK
	    CHUNK
	    CHUNK
	    j4++;
	  } while (j4 < n4);
	}
      }
      {
	unsigned j4=0, n4=n%UNROLL;
	if (n4 > 0) {
	  do {
	    CHUNK
	    j4++;
	  } while (j4 < n4);
	}
      }
      pc_i[k] = total;
    }
    pa_i += stride_a;
    pc_i += stride_c;
  }
}

xor_and xor_and_random(void) {
  static uint64_t next = 1325997111;
  next = next * 1103515249 + 12345;
  return next;
}

void xor_and_mat_random(unsigned m,
		       unsigned n,
		       xor_and *a, unsigned stride_a) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned j=0; j<n; j++) {
      a[i*stride_a + j] = xor_and_random();
    }
  }
}

bool xor_and_mat_equal(unsigned m,
		      unsigned n,
		      const xor_and *a, unsigned stride_a,
		      const xor_and *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned j=0; j<n; j++) {
      if (a[i*stride_a + j] != b[i*stride_b + j]) return false;
    }
  }
  return true;
}
