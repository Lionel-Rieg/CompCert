#include "float_mat.h"
#include <stddef.h>

#define ADD +=
#define MUL *

void REAL_mat_mul1(unsigned m, unsigned n, unsigned p,
		     REAL * restrict c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b) {
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

void REAL_mat_mul2(unsigned m, unsigned n, unsigned p,
		     REAL * restrict c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      REAL total = 0;
      for(unsigned j=0; j<n; j++) {
	total ADD (a[i*stride_a + j] MUL b[j*stride_b + k]);
      }
      c[i*stride_c+k] = total;
    }
  }
}

void REAL_mat_mul3(unsigned m, unsigned n, unsigned p,
		     REAL * restrict c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      REAL total0 = 0, total1 = 0;
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

void REAL_mat_mul4(unsigned m, unsigned n, unsigned p,
		     REAL * c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b) {
  const REAL *pa_i = a;
  REAL * pc_i = c;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const REAL *pb_j_k = b+k, *pa_i_j = pa_i;
      REAL total = 0;
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

void REAL_mat_mul5(unsigned m, unsigned n, unsigned p,
		     REAL * c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b) {
  const REAL *pa_i = a;
  REAL * pc_i = c;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const REAL *pb_j_k = b+k, *pa_i_j = pa_i;
      REAL total = 0;
      for(unsigned j2=0, n2=n/2; j2<n2; j2++) {
	REAL p0 = *pa_i_j MUL *pb_j_k;
	pa_i_j ++;
	pb_j_k += stride_b;
	REAL p1 = *pa_i_j MUL *pb_j_k;
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

void REAL_mat_mul6(unsigned m, unsigned n, unsigned p,
		     REAL * c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b) {
  const REAL *pa_i = a;
  REAL * pc_i = c;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const REAL *pb_j_k = b+k, *pa_i_j = pa_i;
      REAL total = 0;
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
void REAL_mat_mul7(unsigned m, unsigned n, unsigned p,
		     REAL * c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b) {
  const REAL *pa_i = a;
  REAL * pc_i = c;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const REAL *pb_j_k = b+k, *pa_i_j = pa_i;
      REAL total = 0;
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

#undef CHUNK
#define CHUNK \
	    total ADD (*pa_i_j MUL *pb_j_k); \
	    pa_i_j ++; \
	    pb_j_k = (REAL*) ((char*) pb_j_k + stride_b_scaled);

void REAL_mat_mul8(unsigned m, unsigned n, unsigned p,
		     REAL * c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b) {
  const REAL *pa_i = a;
  REAL * pc_i = c;
  size_t stride_b_scaled = sizeof(REAL) * stride_b;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const REAL *pb_j_k = b+k, *pa_i_j = pa_i;
      REAL total = 0;
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
