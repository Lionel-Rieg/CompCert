typedef int comparison(const void *, const void *, void *);

void quicksort (void *const pbase, size_t total_elems, size_t size,
		comparison *cmp, void *arg);
