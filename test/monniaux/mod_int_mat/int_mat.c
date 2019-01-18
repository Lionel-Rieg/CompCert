#include "modint.h"

void modint_mat_mul1(unsigned m, unsigned n, unsigned p,
		     modint * restrict c, unsigned stride_c,
		     const modint *a, unsigned stride_a,
		     const modint *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      c[i*stride_c+k] = 0;
    }
  }
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      for(unsigned j=0; j<n; j++) {
	c[i*stride_c+k] += a[i*stride_a+j] * b[j*stride_b+k]; 
      }
    }
  }
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      c[i*stride_c+k] %= MODULUS;
    }
  }  
}

void modint_mat_mul2(unsigned m, unsigned n, unsigned p,
		     modint * restrict c, unsigned stride_c,
		     const modint *a, unsigned stride_a,
		     const modint *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      modint total = 0;
      for(unsigned j=0; j<n; j++) {
	total += a[i*stride_a + j] * b[j*stride_b + k];
      }
      c[i*stride_c+k] = total % MODULUS;
    }
  }
}

void modint_mat_mul3(unsigned m, unsigned n, unsigned p,
		     modint * restrict c, unsigned stride_c,
		     const modint *a, unsigned stride_a,
		     const modint *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      modint total0 = 0, total1 = 0;
      unsigned j;
      for(j=0; j+1<n; j+=2) {
	total0 += a[i*stride_a + j] * b[j*stride_b + k];
	total1 += a[i*stride_a + (j+1)] * b[(j+1)*stride_b + k];
      }
      if (j < n) {
	total0 += a[i*stride_a + j] * b[j*stride_b + k];
      }
      c[i*stride_c+k] = (total0+total1) % MODULUS;
    }
  }
}

void modint_mat_mul4(unsigned m, unsigned n, unsigned p,
		     modint * c, unsigned stride_c,
		     const modint *a, unsigned stride_a,
		     const modint *b, unsigned stride_b) {
  const modint *pa_i = a;
  modint * pc_i = c;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const modint *pb_j_k = b+k, *pa_i_j = pa_i;
      modint total = 0;
      for(unsigned j=0; j<n; j++) {
	total += *pa_i_j * *pb_j_k;
	pa_i_j ++;
	pb_j_k += stride_b;
      }
      pc_i[k] = total % MODULUS;
    }
    pa_i += stride_a;
    pc_i += stride_c;
  }
}

void modint_mat_mul5(unsigned m, unsigned n, unsigned p,
		     modint * c, unsigned stride_c,
		     const modint *a, unsigned stride_a,
		     const modint *b, unsigned stride_b) {
  const modint *pa_i = a;
  modint * pc_i = c;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const modint *pb_j_k = b+k, *pa_i_j = pa_i;
      modint total = 0;
      for(unsigned j2=0, n2=n/2; j2<n2; j2++) {
	modint p0 = *pa_i_j * *pb_j_k;
	pa_i_j ++;
	pb_j_k += stride_b;
	modint p1 = *pa_i_j * *pb_j_k;
	pa_i_j ++;
	pb_j_k += stride_b;
	total += p0 + p1;
      }
      if (n%2) {
	total += *pa_i_j * *pb_j_k;
      }
      pc_i[k] = total % MODULUS;
    }
    pa_i += stride_a;
    pc_i += stride_c;
  }
}

void modint_mat_mul6(unsigned m, unsigned n, unsigned p,
		     modint * c, unsigned stride_c,
		     const modint *a, unsigned stride_a,
		     const modint *b, unsigned stride_b) {
  const modint *pa_i = a;
  modint * pc_i = c;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const modint *pb_j_k = b+k, *pa_i_j = pa_i;
      modint total = 0;
      unsigned j2=0, n2=n/2;
      if (n2 > 0) {
	do {
	  total += *pa_i_j * *pb_j_k;
	  pa_i_j ++;
	  pb_j_k += stride_b;
	  total += *pa_i_j * *pb_j_k;
	  pa_i_j ++;
	  pb_j_k += stride_b;
	  j2++;
	} while (j2 < n2);
      }
      if (n%2) {
	total += *pa_i_j * *pb_j_k;
      }
      pc_i[k] = total % MODULUS;
    }
    pa_i += stride_a;
    pc_i += stride_c;
  }
}

void modint_mat_mul7(unsigned m, unsigned n, unsigned p,
		     modint * c, unsigned stride_c,
		     const modint *a, unsigned stride_a,
		     const modint *b, unsigned stride_b) {
  const modint *pa_i = a;
  modint * pc_i = c;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const modint *pb_j_k = b+k, *pa_i_j = pa_i;
      modint total = 0;
      {
	unsigned j4=0, n4=n/4;
	if (n4 > 0) {
	  do {
	    total += *pa_i_j * *pb_j_k;
	    pa_i_j ++;
	    pb_j_k += stride_b;
	    total += *pa_i_j * *pb_j_k;
	    pa_i_j ++;
	    pb_j_k += stride_b;
	    total += *pa_i_j * *pb_j_k;
	    pa_i_j ++;
	    pb_j_k += stride_b;
	    total += *pa_i_j * *pb_j_k;
	    pa_i_j ++;
	    pb_j_k += stride_b;
	    j4++;
	  } while (j4 < n4);
	}
      }
      {
	unsigned j4=0, n4=n%4;
	if (n4 > 0) {
	  do {
	    total += *pa_i_j * *pb_j_k;
	    pa_i_j ++;
	    pb_j_k += stride_b;
	    j4++;
	  } while (j4 < n4);
	}
      }
      pc_i[k] = total % MODULUS;
    }
    pa_i += stride_a;
    pc_i += stride_c;
  }
}

modint modint_random(void) {
  static uint64_t next = 1325997111;
  next = next * 1103515245 + 12345;
  return next % MODULUS;
}

void modint_mat_random(unsigned m,
		       unsigned n,
		       modint *a, unsigned stride_a) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned j=0; j<n; j++) {
      a[i*stride_a + j] = modint_random();
    }
  }
}

bool modint_mat_equal(unsigned m,
		      unsigned n,
		      const modint *a, unsigned stride_a,
		      const modint *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned j=0; j<n; j++) {
      if (a[i*stride_a + j] != b[i*stride_b + j]) return false;
    }
  }
  return true;
}
