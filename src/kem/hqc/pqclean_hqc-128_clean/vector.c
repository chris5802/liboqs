#include "parameters.h"
#include "parsing.h"
#include "randombytes.h"
#include "vector.h"
#include <stdint.h>
#include <string.h>
/**
 * @file vector.c
 * @brief Implementation of vectors sampling and some utilities for the HQC scheme
 */


static uint32_t m_val[75] = { 243079, 243093, 243106, 243120, 243134, 243148, 243161, 243175, 243189, 243203, 243216, 243230, 243244, 243258, 243272, 243285, 243299, 243313, 243327, 243340, 243354, 243368, 243382, 243396, 243409, 243423, 243437, 243451, 243465, 243478, 243492, 243506, 243520, 243534, 243547, 243561, 243575, 243589, 243603, 243616, 243630, 243644, 243658, 243672, 243686, 243699, 243713, 243727, 243741, 243755, 243769, 243782, 243796, 243810, 243824, 243838, 243852, 243865, 243879, 243893, 243907, 243921, 243935, 243949, 243962, 243976, 243990, 244004, 244018, 244032, 244046, 244059, 244073, 244087, 244101 };

/**
 * @brief Constant-time comparison of two integers v1 and v2
 *
 * Returns 1 if v1 is equal to v2 and 0 otherwise
 * https://gist.github.com/sneves/10845247
 *
 * @param[in] v1
 * @param[in] v2
 */
static inline uint32_t compare_u32(uint32_t v1, uint32_t v2) {
    return 1 ^ ((uint32_t)((v1 - v2) | (v2 - v1)) >> 31);
}



/**
 * @brief Constant-time Barrett reduction modulo PARAM_N.
 *
 * Reduces \p x modulo PARAM_N using the precomputed value PARAM_N_MU = ⌊2^32 / PARAM_N⌋.
 *
 * @param[in] x Input value to reduce.
 * @return x mod PARAM_N in constant time.
 */
static inline uint32_t barrett_reduce(uint32_t x) {
    uint64_t q = ((uint64_t)x * PARAM_N_MU) >> 32;
    uint32_t r = x - (uint32_t)(q * PARAM_N);

    uint32_t reduce_flag = (((r - PARAM_N) >> 31) ^ 1);
    uint32_t mask = -reduce_flag;
    r -= mask & PARAM_N;
    return r;
}


/**
 * @brief Sets bits in a vector based on a support set.
 *
 * Writes `weight` positions from `support` into the bit-vector `v`.
 * Each index in `support` sets a corresponding bit in `v`.
 *
 * @param[out] v       Output vector.
 * @param[in]  support Array of bit indices to set.
 * @param[in]  weight  Number of positions to set.
 */
void vect_write_support_to_vector(uint64_t *v, uint32_t *support, uint16_t weight) {
    uint32_t index_tab[PARAM_OMEGA_R] = {0};
    uint64_t bit_tab[PARAM_OMEGA_R] = {0};

    for (size_t i = 0; i < weight; i++) {
        index_tab[i] = support[i] >> 6;
        int32_t pos = support[i] & 0x3f;
        bit_tab[i] = ((uint64_t)1) << pos;
    }

    uint64_t val = 0;
    for (uint32_t i = 0; i < VEC_N_SIZE_64; i++) {
        val = 0;
        for (uint32_t j = 0; j < weight; j++) {
            uint32_t tmp = i - index_tab[j];
            int val1 = 1 ^ ((tmp | -tmp) >> 31);
            uint64_t mask = -val1;
            val |= (bit_tab[j] & mask);
        }
        v[i] |= val;
    }
}

static uint64_t single_bit_mask(uint32_t pos) {
    uint64_t ret = 0;
    uint64_t mask = 1;
    uint64_t tmp;

    for (size_t i = 0; i < 64; ++i) {
        tmp = pos - i;
        tmp = 0 - (1 - ((uint64_t)(tmp | (0 - tmp)) >> 63));
        ret |= mask & tmp;
        mask <<= 1;
    }

    return ret;
}

static inline uint32_t cond_sub(uint32_t r, uint32_t n) {
    uint32_t mask;
    r -= n;
    mask = 0 - (r >> 31);
    return r + (n & mask);
}

static inline uint32_t reduce(uint32_t a, size_t i) {
    uint32_t q, n, r;
    q = ((uint64_t) a * m_val[i]) >> 32;
    n = (uint32_t)(PARAM_N - i);
    r = a - q * n;
    return cond_sub(r, n);
}

/**
 * @brief Generates a vector of a given Hamming weight
 *
 * Implementation of Algorithm 5 in https://eprint.iacr.org/2021/1631.pdf
 *
 * @param[in] ctx Pointer to the context of the seed expander
 * @param[in] v Pointer to an array
 * @param[in] weight Integer that is the Hamming weight
 */
void PQCLEAN_HQC128_CLEAN_vect_set_random_fixed_weight(seedexpander_state *ctx, uint64_t *v, uint16_t weight) {
    uint8_t rand_bytes[4 * PARAM_OMEGA_R] = {0}; // to be interpreted as PARAM_OMEGA_R 32-bit unsigned ints
    uint32_t support[PARAM_OMEGA_R] = {0};
    uint32_t index_tab [PARAM_OMEGA_R] = {0};
    uint64_t bit_tab [PARAM_OMEGA_R] = {0};
    uint32_t pos, found, mask32, tmp;
    uint64_t mask64, val;

    PQCLEAN_HQC128_CLEAN_seedexpander(ctx, rand_bytes, 4 * weight);

    //printf("-------- generate support vector - orignal --------");

    for (size_t i = 0; i < weight; ++i) {
        support[i] = rand_bytes[4 * i];
        support[i] |= rand_bytes[4 * i + 1] << 8;
        support[i] |= (uint32_t)rand_bytes[4 * i + 2] << 16;
        support[i] |= (uint32_t)rand_bytes[4 * i + 3] << 24;
        support[i] = (uint32_t)(i + reduce(support[i], i)); // use constant-tme reduction
        //printf("i = %zu, support[i] = %u\n", i, support[i]);
        
    }


    for (size_t i = (weight - 1); i-- > 0;) {
        found = 0;

        for (size_t j = i + 1; j < weight; ++j) {
            found |= compare_u32(support[j], support[i]);
        }

        mask32 = 0 - found;
        support[i] = (mask32 & i) ^ (~mask32 & support[i]);
    }

    for (size_t i = 0; i < weight; ++i) {
        index_tab[i] = support[i] >> 6;
        pos = support[i] & 0x3f;
        bit_tab[i] = single_bit_mask(pos); // avoid secret shift
    }

    for (size_t i = 0; i < VEC_N_SIZE_64; ++i) {
        val = 0;
        for (size_t j = 0; j < weight; ++j) {
            tmp = (uint32_t)(i - index_tab[j]);
            tmp = 1 ^ ((uint32_t)(tmp | (0 - tmp)) >> 31);
            mask64 = 0 - (uint64_t)tmp;
            val |= (bit_tab[j] & mask64);
        }
        v[i] |= val;
    }
}

/**
 * @brief Generates a random support set with uniform and unbiased sampling.
 *
 * This function implements a rejection sampling algorithm to generate `weight`
 * distinct indices uniformly at random from the interval [0, PARAM_N).
 * It ensures that the output is non-biased and the values are uniformly distributed.
 *
 * Internally, it samples 24-bit random values and rejects any value ≥ UTILS_REJECTION_THRESHOLD,
 * where the threshold is precomputed as:
 * \f[
 * t = \left\lfloor \frac{2^{24}}{\text{PARAM\_N}} \right\rfloor \times \text{PARAM\_N}
 * \f]
 *
 * @param[in,out] ctx     SHAKE256 XOF context used for random byte generation.
 * @param[out]    support Output array to store the `weight` unique indices.
 * @param[in]     weight  Desired Hamming weight.
 */
void PQCLEAN_HQC128_CLEAN_vect_generate_random_support_rejection(seedexpander_state *ctx, uint32_t *support, uint16_t weight) {
    size_t random_bytes_size = 3 * weight;
    uint8_t rand_bytes[3 * PARAM_OMEGA_R] = {0};
    uint8_t inc;
    size_t i, j;

    //printf("-------- generate support vector - rejection --------");
    i = 0;
    j = random_bytes_size;
    while (i < weight) {
        do {
            if (j == random_bytes_size) {
                PQCLEAN_HQC128_CLEAN_seedexpander(ctx, rand_bytes, random_bytes_size);
                j = 0;
            }

            support[i] = ((uint32_t)rand_bytes[j++]) << 16;
            support[i] |= ((uint32_t)rand_bytes[j++]) << 8;
            support[i] |= rand_bytes[j++];
            //printf("i = %zu, support[i] = %u\n", i, support[i]);

        } while (support[i] >= UTILS_REJECTION_THRESHOLD);

        support[i] = barrett_reduce(support[i]);

        inc = 1;
        for (size_t k = 0; k < i; k++) {
            if (support[k] == support[i]) {
                inc = 0;
            }
        }
        i += inc;
    }
}


/**
 * @brief Generates a random support set of distinct indices.
 *
 * This implements the **GenerateRandomSupport** algorithm from the specification.
 *
 * @param[in,out] ctx     Initialized SHAKE256 XOF context used for randomness.
 * @param[out]    support Output array of unique indices (the support set).
 * @param[in]     weight  Number of elements to generate (Hamming weight).
 */
void PQCLEAN_HQC128_CLEAN_vect_generate_random_support_fisheryates(seedexpander_state *ctx, uint32_t *support, uint16_t weight) {
    uint32_t rand_u32[PARAM_OMEGA_R] = {0};

    PQCLEAN_HQC128_CLEAN_seedexpander(ctx, (uint8_t *)rand_u32, 4 * weight);

    for (size_t i = 0; i < weight; ++i) {
        uint64_t buff = rand_u32[i];
        support[i] = i + ((buff * (PARAM_N - i)) >> 32);
    }

    for (int32_t i = (weight - 1); i-- > 0;) {
        uint32_t found = 0;

        for (size_t j = i + 1; j < weight; ++j) {
            found |= compare_u32(support[j], support[i]);
        }

        uint32_t mask = -found;
        support[i] = (mask & i) ^ (~mask & support[i]);
    }
}

/**
 * @brief Generates a random support set using Constant-Time Uniform Sampling (CTUS).
 *
 * This function implements the "oversample and filter" strategy in a style consistent
 * with the existing codebase. It generates T_over candidates, removes duplicates by
 * marking them with an invalid value, and then performs a constant-time compaction
 * to gather the unique elements.
 *
 * @param[in,out] ctx     Initialized SHAKE256 XOF context.
 * @param[out]    support Output array of unique indices.
 * @param[in]     weight  Number of elements to generate.
 */
void PQCLEAN_HQC128_CLEAN_vect_generate_random_support_ctus(seedexpander_state *ctx, uint32_t *support, uint16_t weight)
{
    const size_t t_over = 2 * weight; /// 參數之後要調
    uint32_t candidates[2 * PARAM_OMEGA_R];
    uint32_t rand_u32[2 * PARAM_OMEGA_R] = {0};
    uint32_t unique_candidates[2 * PARAM_OMEGA_R] = {0};
    size_t unique_count = 0;
    size_t i, j;

    // 1. Generate T_over candidates from a single random buffer
    PQCLEAN_HQC128_CLEAN_seedexpander(ctx, (uint8_t *)rand_u32, 4 * t_over);

    for (i = 0; i < t_over; ++i)
    {
        candidates[i] = barrett_reduce(rand_u32[i]);
        
    }

    // 2. Constant-time deduplication: Mark duplicates with PARAM_N
    for (i = 0; i < t_over; ++i)
    {
        for (j = i + 1; j < t_over; ++j)
        {
            uint32_t are_equal = compare_u32(candidates[i], candidates[j]);
            uint32_t mask = -are_equal;
            candidates[j] = (mask & PARAM_N) | (~mask & candidates[j]);
        }
    }

    // 3. Constant-time compaction
    // This approach iterates through all candidates and conditionally writes valid ones
    // to the next available slot in `unique_candidates`. The write position is
    // determined by a constant-time comparison, thus avoiding secret-dependent branches.
    // While correct, this O(n^2) compaction is less efficient than a sorting network.
    for (i = 0; i < t_over; ++i)
    {
        uint32_t is_valid = 1 - compare_u32(candidates[i], PARAM_N);
        uint32_t mask = -is_valid;

        for (j = 0; j < t_over; ++j)
        {
            uint32_t is_current_slot = compare_u32(j, unique_count);
            uint32_t write_mask = is_current_slot & mask;
            
            unique_candidates[j] = (write_mask & candidates[i]) | (~write_mask & unique_candidates[j]);
        }
        unique_count += is_valid;
    }

    // 4. Copy the required number of unique elements to the final support array
    for (i = 0; i < weight; ++i)
    {
        support[i] = unique_candidates[i];
        
    }
}

/**
 * @brief Generates a random support set using Fixed-N Rejection Sampling.
 *
 * This function adapts rejection sampling into a fixed-iteration structure to ensure
 * constant-time execution. It attempts to generate a value in each iteration and adds
 * it to the support set if it is valid and unique. All conditional logic is
 * implemented with bitmasks to prevent timing side channels.
 *
 * @param[in,out] ctx     Initialized SHAKE256 XOF context.
 * @param[out]    support Output array of unique indices.
 * @param[in]     weight  Number of elements to generate.
 */
void PQCLEAN_HQC128_CLEAN_vect_generate_random_support_fixed_n(seedexpander_state *ctx, uint32_t *support, uint16_t weight)
{
    const size_t n_iterations = 2 * weight;
    const size_t random_bytes_size = 3 * n_iterations;
    uint8_t rand_bytes[3 * 2 * PARAM_OMEGA_R];
    size_t count = 0;
    size_t random_byte_idx = 0;
    size_t i, j;

    // 1. Pre-fill support with an invalid value
    for (i = 0; i < weight; ++i)
    {
        support[i] = PARAM_N;
    }

    PQCLEAN_HQC128_CLEAN_seedexpander(ctx, rand_bytes, random_bytes_size);

    // 2. Fixed iteration loop
    for (i = 0; i < n_iterations; ++i)
    {
        uint32_t c = ((uint32_t)rand_bytes[random_byte_idx++]) << 16;
        c |= ((uint32_t)rand_bytes[random_byte_idx++]) << 8;
        c |= rand_bytes[random_byte_idx++];

        // Perform checks using constant-time masks
        uint32_t accept_mask = -((c - UTILS_REJECTION_THRESHOLD) >> 31);
        c = barrett_reduce(c);

        uint32_t is_duplicate = 0;
        for (j = 0; j < weight; ++j)
        {
            is_duplicate |= compare_u32(c, support[j]);
        }
        uint32_t unique_mask = 1 - is_duplicate;

        uint32_t space_available_mask = -((uint32_t)(count - weight) >> 31);
        uint32_t final_add_mask = accept_mask & unique_mask & space_available_mask;

        // 3. Constant-time update of the support array
        // Conditionally write the new candidate `c` to the position `support[count]`.
        for (j = 0; j < weight; ++j)
        {
            uint32_t is_current_slot = compare_u32(j, count);
            uint32_t write_mask = is_current_slot & final_add_mask;
            support[j] = (write_mask & c) | (~write_mask & support[j]);
        }

        // 4. Constant-time increment of the counter
        count += (final_add_mask & 1);
    }
}


/**
 * @brief Samples a vector of a given Hamming weight using CTUS.
 *
 * @param[in] ctx Pointer to the context of the seed expander
 * @param[in] v Pointer to an array
 * @param[in] weight Integer that is the Hamming weight
 */
void PQCLEAN_HQC128_CLEAN_vect_sample_fixed_weight_ctus(seedexpander_state *ctx, uint64_t *v, uint16_t weight)
{
    uint32_t support[PARAM_OMEGA_R] = {0};
    PQCLEAN_HQC128_CLEAN_vect_generate_random_support_ctus(ctx, support, weight);
    vect_write_support_to_vector(v, support, weight);
}


/**
 * @brief Samples a vector of a given Hamming weight using Fixed-N Rejection Sampling.
 *
 * @param[in] ctx Pointer to the context of the seed expander
 * @param[in] v Pointer to an array
 * @param[in] weight Integer that is the Hamming weight
 */
void PQCLEAN_HQC128_CLEAN_vect_sample_fixed_weight_fixed_n(seedexpander_state *ctx, uint64_t *v, uint16_t weight)
{
    uint32_t support[PARAM_OMEGA_R] = {0};
    PQCLEAN_HQC128_CLEAN_vect_generate_random_support_fixed_n(ctx, support, weight);
    vect_write_support_to_vector(v, support, weight);
}


void PQCLEAN_HQC128_CLEAN_vect_sample_fixed_weight_rejection(seedexpander_state *ctx, uint64_t *v, uint16_t weight){
    uint32_t support[PARAM_OMEGA_R] = {0};
    PQCLEAN_HQC128_CLEAN_vect_generate_random_support_rejection(ctx, support, weight);
    vect_write_support_to_vector(v, support, weight);
}


void PQCLEAN_HQC128_CLEAN_vect_sample_fixed_weight_fisheryates(seedexpander_state *ctx, uint64_t *v, uint16_t weight){
    uint32_t support[PARAM_OMEGA_R] = {0};
    PQCLEAN_HQC128_CLEAN_vect_generate_random_support_fisheryates(ctx, support, weight);
    vect_write_support_to_vector(v, support, weight);
}

/**
 * @brief Generates a random vector of dimension <b>PARAM_N</b>
 *
 * This function generates a random binary vector of dimension <b>PARAM_N</b>. It generates a random
 * array of bytes using the PQCLEAN_HQC128_CLEAN_seedexpander function, and drop the extra bits using a mask.
 *
 * @param[in] v Pointer to an array
 * @param[in] ctx Pointer to the context of the seed expander
 */
void PQCLEAN_HQC128_CLEAN_vect_set_random(seedexpander_state *ctx, uint64_t *v) {
    uint8_t rand_bytes[VEC_N_SIZE_BYTES] = {0};

    PQCLEAN_HQC128_CLEAN_seedexpander(ctx, rand_bytes, VEC_N_SIZE_BYTES);

    PQCLEAN_HQC128_CLEAN_load8_arr(v, VEC_N_SIZE_64, rand_bytes, VEC_N_SIZE_BYTES);
    v[VEC_N_SIZE_64 - 1] &= RED_MASK;
}



/**
 * @brief Adds two vectors
 *
 * @param[out] o Pointer to an array that is the result
 * @param[in] v1 Pointer to an array that is the first vector
 * @param[in] v2 Pointer to an array that is the second vector
 * @param[in] size Integer that is the size of the vectors
 */
void PQCLEAN_HQC128_CLEAN_vect_add(uint64_t *o, const uint64_t *v1, const uint64_t *v2, size_t size) {
    for (size_t i = 0; i < size; ++i) {
        o[i] = v1[i] ^ v2[i];
    }
}



/**
 * @brief Compares two vectors
 *
 * @param[in] v1 Pointer to an array that is first vector
 * @param[in] v2 Pointer to an array that is second vector
 * @param[in] size Integer that is the size of the vectors
 * @returns 0 if the vectors are equal and 1 otherwise
 */
uint8_t PQCLEAN_HQC128_CLEAN_vect_compare(const uint8_t *v1, const uint8_t *v2, size_t size) {
    uint16_t r = 0x0100;

    for (size_t i = 0; i < size; i++) {
        r |= v1[i] ^ v2[i];
    }

    return (r - 1) >> 8;
}



/**
 * @brief Resize a vector so that it contains <b>size_o</b> bits
 *
 * @param[out] o Pointer to the output vector
 * @param[in] size_o Integer that is the size of the output vector in bits
 * @param[in] v Pointer to the input vector
 * @param[in] size_v Integer that is the size of the input vector in bits
 */
void PQCLEAN_HQC128_CLEAN_vect_resize(uint64_t *o, uint32_t size_o, const uint64_t *v, uint32_t size_v) {
    uint64_t mask = 0x7FFFFFFFFFFFFFFF;
    size_t val = 0;
    if (size_o < size_v) {

        if (size_o % 64) {
            val = 64 - (size_o % 64);
        }

        memcpy(o, v, VEC_N1N2_SIZE_BYTES);

        for (size_t i = 0; i < val; ++i) {
            o[VEC_N1N2_SIZE_64 - 1] &= (mask >> i);
        }
    } else {
        memcpy(o, v, 8 * CEIL_DIVIDE(size_v, 64));
    }
}
