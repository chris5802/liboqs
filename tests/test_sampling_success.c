// SPDX-License-Identifier: MIT

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <oqs/oqs.h>

#include "../src/kem/hqc/pqclean_hqc-128_clean/api.h"
#include "../src/kem/hqc/pqclean_hqc-128_clean/vector.h"
#include "../src/kem/hqc/pqclean_hqc-128_clean/shake_prng.h"
#include "../src/kem/hqc/pqclean_hqc-128_clean/parameters.h"

// Forward declaration for the testable functions
int PQCLEAN_HQC128_CLEAN_vect_generate_random_support_ctus_testable(seedexpander_state *ctx, uint32_t *support, uint16_t weight, float k_factor, float attempts_factor);
int PQCLEAN_HQC128_CLEAN_vect_generate_random_support_fixed_n_testable(seedexpander_state *ctx, uint32_t *support, uint16_t weight, float n_iterations_factor);


static void test_ctus_sampling(FILE *output_stream, seedexpander_state *ctx, uint16_t weight, long long iterations, float k_factor, float attempts_factor) {
    long long successes = 0;
    long long failures = 0;
    uint32_t *support = malloc(weight * sizeof(uint32_t));
    if (support == NULL) {
        fprintf(stderr, "Failed to allocate memory for support vector in CTUS test.\n");
        return;
    }

    clock_t start = clock();

    for (long long i = 0; i < iterations; ++i) {
        int ret = PQCLEAN_HQC128_CLEAN_vect_generate_random_support_ctus_testable(ctx, support, weight, k_factor, attempts_factor);
        if (ret == 0) {
            successes++;
        } else {
            failures++;
        }
    }

    clock_t end = clock();
    double time_spent = (double)(end - start) / CLOCKS_PER_SEC;
    free(support);

    fprintf(output_stream, "CTUS,%d,k_%.2f,att_%.2f,%lld,%lld,%.4f,%.6f\n",
           weight, k_factor, attempts_factor, successes, failures,
           (double)successes * 100.0 / (double)iterations,
           (time_spent * 1000.0) / iterations);
}

static void test_fixed_n_sampling(FILE *output_stream, seedexpander_state *ctx, uint16_t weight, long long iterations, float n_iterations_factor) {
    long long successes = 0;
    long long failures = 0;
    uint32_t *support = malloc(weight * sizeof(uint32_t));
    if (support == NULL) {
        fprintf(stderr, "Failed to allocate memory for support vector in Fixed-N test.\n");
        return;
    }

    clock_t start = clock();

    for (long long i = 0; i < iterations; ++i) {
        int ret = PQCLEAN_HQC128_CLEAN_vect_generate_random_support_fixed_n_testable(ctx, support, weight, n_iterations_factor);
        if (ret == 0) {
            successes++;
        } else {
            failures++;
        }
    }

    clock_t end = clock();
    double time_spent = (double)(end - start) / CLOCKS_PER_SEC;
    free(support);

    fprintf(output_stream, "Fixed-N,%d,n_iter_%.2f,,%lld,%lld,%.4f,%.6f\n",
           weight, n_iterations_factor, successes, failures,
           (double)successes * 100.0 / (double)iterations,
           (time_spent * 1000.0) / iterations);
}

int main(int argc, char **argv) {
    FILE *output_stream = stdout;
    if (argc > 1) {
        output_stream = fopen(argv[1], "w");
        if (output_stream == NULL) {
            fprintf(stderr, "ERROR: Cannot open output file %s\n", argv[1]);
            return EXIT_FAILURE;
        }
        printf("Writing results to %s\n", argv[1]);
    }

    uint8_t seed[48];
    for (int i = 0; i < 48; i++) {
        seed[i] = (uint8_t)i;
    }
    seedexpander_state ctx;
    PQCLEAN_HQC128_CLEAN_seedexpander_init(&ctx, seed, 48);

    long long iterations = 500000; // 500k iterations for higher statistical significance
    uint16_t weights_to_test[] = {66, 75, 100, 114, 131, 149};

    fprintf(output_stream, "Algorithm,Weight,Parameter 1,Parameter 2,Successes,Failures,Success Rate (%%),Avg. Time (ms)\n");

    float hyperfine_factors[] = {1.01f, 1.02f, 1.03f, 1.04f, 1.05f, 1.06f, 1.07f, 1.08f, 1.09f, 1.10f, 1.11f, 1.12f, 1.13f, 1.14f, 1.15f};
    size_t num_factors = sizeof(hyperfine_factors)/sizeof(hyperfine_factors[0]);

    for (size_t w_idx = 0; w_idx < sizeof(weights_to_test)/sizeof(weights_to_test[0]); ++w_idx) {
        uint16_t current_weight = weights_to_test[w_idx];
        printf("Testing for weight: %u\n", current_weight);

        // --- Test CTUS (diagonal k_factor == attempts_factor) ---
        for (size_t i = 0; i < num_factors; ++i) {
            test_ctus_sampling(output_stream, &ctx, current_weight, iterations, hyperfine_factors[i], hyperfine_factors[i]);
        }

        // --- Test Fixed-N ---
        for (size_t i = 0; i < num_factors; ++i) {
            test_fixed_n_sampling(output_stream, &ctx, current_weight, iterations, hyperfine_factors[i]);
        }
    }

    if (output_stream != stdout) {
        fclose(output_stream);
    }

    printf("Hyperfine tests finished.\n");

    return EXIT_SUCCESS;
}