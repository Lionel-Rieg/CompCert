#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <inttypes.h>
#include "../cycles.h"
#include "sha-256.h"

struct string_vector {
	const char *input;
	const char *output;
};

static const struct string_vector STRING_VECTORS[] = {
	{
		"",
		"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
	},
	{
		"abc",
		"ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
	},
	{
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		"a8ae6e6ee929abea3afcfc5258c8ccd6f85273e0d4626d26c7279f3250f77c8e"
	},
	{
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcde",
		"057ee79ece0b9a849552ab8d3c335fe9a5f1c46ef5f1d9b190c295728628299c"
	},
	{
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0",
		"2a6ad82f3620d3ebe9d678c812ae12312699d673240d5be8fac0910a70000d93"
	},
	{
		"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
		"248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
	},
	{
		"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno"
		"ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
		"cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
	}
};

#define LARGE_MESSAGES 1
#define LARGER_MESSAGES 0

static uint8_t data1[] = { 0xbd };
static uint8_t data2[] = { 0xc9, 0x8c, 0x8e, 0x55 };
static uint8_t data7[1000];
static uint8_t data8[1000];
static uint8_t data9[1005];
#if LARGE_MESSAGES
#define SIZEOF_DATA11 536870912
#define SIZEOF_DATA12 1090519040
#define SIZEOF_DATA13 1610612798
static uint8_t * data11;
static uint8_t * data12;
static uint8_t * data13;
#endif

struct vector {
	const uint8_t *input;
	size_t input_len;
	const char *output;
};

static struct vector vectors[] = {
	{
		data1,
		sizeof data1,
		"68325720aabd7c82f30f554b313d0570c95accbb7dc4b5aae11204c08ffe732b"
	},
	{
		data2,
		sizeof data2,
		"7abc22c0ae5af26ce93dbb94433a0e0b2e119d014f8e7f65bd56c61ccccd9504"
	},
	{
		data7,
		55,
		"02779466cdec163811d078815c633f21901413081449002f24aa3e80f0b88ef7"
	},
	{
		data7,
		56,
		"d4817aa5497628e7c77e6b606107042bbba3130888c5f47a375e6179be789fbb"
	},
	{
		data7,
		57,
		"65a16cb7861335d5ace3c60718b5052e44660726da4cd13bb745381b235a1785"
	},
	{
		data7,
		64,
		"f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"
	},
	{
		data7,
		sizeof data7,
		"541b3e9daa09b20bf85fa273e5cbd3e80185aa4ec298e765db87742b70138a53"
	},
	{
		data8,
		sizeof data8,
		"c2e686823489ced2017f6059b8b239318b6364f6dcd835d0a519105a1eadd6e4"
	},
	{
		data9,
		sizeof data9,
		"f4d62ddec0f3dd90ea1380fa16a5ff8dc4c54b21740650f24afc4120903552b0"
	},
#if LARGE_MESSAGES
	{
		NULL,
		/* too big
		1000000,
		"d29751f2649b32ff572b5e0a9f541ea660a50f94ff0beedfb0b692b924cc8025"
		*/
		50000,
		"5b4b67b5d68e02c992760de07640472efe53a7f7553865f83262d0a74efc3e5d"
	},
#if LARGER_MESSAGES
	{
		NULL,
		SIZEOF_DATA11,
		"15a1868c12cc53951e182344277447cd0979536badcc512ad24c67e9b2d4f3dd"
	},
	{
		NULL,
		SIZEOF_DATA12,
		"461c19a93bd4344f9215f5ec64357090342bc66b15a148317d276e31cbc20b53"
	},
	{
		NULL,
		SIZEOF_DATA13,
		"c23ce8a7895f4b21ec0daf37920ac0a262a220045a03eb2dfed48ef9b05aabea"
	}
#endif
#endif
};

#if LARGE_MESSAGES
static void *my_malloc(size_t size) {
  void *p=malloc(size);
  if (p==0) {
    fprintf(stderr, "malloc(%zu) failed\n", size);
    abort();
  }
  return p;
}
#endif

static void construct_binary_messages(void)
{
	memset(data7, 0x00, sizeof data7);
	memset(data8, 0x41, sizeof data8);
	memset(data9, 0x55, sizeof data9);
#if LARGE_MESSAGES
#if LARGER_MESSAGES
	/*
	 * Heap allocation as a workaround for some linkers not liking
	 * large BSS segments.
	 */
	data11 = my_malloc(SIZEOF_DATA11);
	data12 = my_malloc(SIZEOF_DATA12);
	data13 = my_malloc(SIZEOF_DATA13);
	memset(data11, 0x5a, SIZEOF_DATA11);
	memset(data12, 0x00, SIZEOF_DATA12);
	memset(data13, 0x42, SIZEOF_DATA13);
	vectors[9].input = data12;
	vectors[10].input = data11;
	vectors[11].input = data12;
	vectors[12].input = data13;
#else
	vectors[9].input = data12 = my_malloc(vectors[9].input_len);
	memset(data12, 0x00, vectors[9].input_len);
#endif
#endif
}

static void destruct_binary_messages(void)
{
#if LARGE_MESSAGES
#if LARGER_MESSAGES
	free(data11);
	free(data12);
	free(data13);
#else
	free(data12);
#endif
#endif
}

static void hash_to_string(char string[65], const uint8_t hash[32])
{
	size_t i;
	for (i = 0; i < 32; i++) {
		string += sprintf(string, "%02x", hash[i]);
	}
}	

static cycle_t cycle_total, cycle_start_time;

static void cycle_count_start(void) {
  cycle_start_time=get_cycle();
}

static void cycle_count_end(void) {
  cycle_total += get_cycle()-cycle_start_time;
}

static int string_test(const char input[], const char output[])
{
	uint8_t hash[32];
	char hash_string[65];

	cycle_count_start();
	calc_sha_256(hash, input, strlen(input));
	cycle_count_end();
	
	hash_to_string(hash_string, hash);
	printf("input: %s\n", input);
	printf("hash : %s\n", hash_string);
	if (strcmp(output, hash_string)) {
		printf("FAILURE!\n\n");
		return 1;
	} else {
		printf("SUCCESS!\n\n");
		return 0;
	}		
}

/*
 * Limitation:
 * - The variable input_len will be truncated to its LONG_BIT least
 * significant bits in the print output. This will never be a problem
 * for values that in practice are less than 2^32 - 1. Rationale: ANSI
 * C-compatibility and keeping it simple.
 */
static int test(const uint8_t * input, size_t input_len, const char output[])
{
	uint8_t hash[32];
	char hash_string[65];

	cycle_count_start();
	calc_sha_256(hash, input, input_len);
	cycle_count_end();

	hash_to_string(hash_string, hash);
	printf("input starts with 0x%02x, length %lu\n", *input, (unsigned long) input_len);
	printf("hash : %s\n", hash_string);
	if (strcmp(output, hash_string)) {
		printf("FAILURE!\n\n");
		return 1;
	} else {
		printf("SUCCESS!\n\n");
		return 0;
	}
}

int main(void)
{
        cycle_count_config();
	size_t i;
	for (i = 0; i < (sizeof STRING_VECTORS / sizeof (struct string_vector)); i++) {
		const struct string_vector *vector = &STRING_VECTORS[i];
		if (string_test(vector->input, vector->output))
		  {} /* DM return 1; */
	}
	construct_binary_messages();
	for (i = 0; i < (sizeof vectors / sizeof (struct vector)); i++) {
		const struct vector *vector = &vectors[i];
		if (test(vector->input, vector->input_len, vector->output))
		{ /* DM
			destruct_binary_messages();
			return 1; */
		}
	}
	destruct_binary_messages();
	printf("total cycles : %" PRIu64 "\n", cycle_total);
  print_all();
	return 0;
}
