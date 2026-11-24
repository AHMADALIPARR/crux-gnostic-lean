/* SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0 */
/* libcrux: C ABI of the CRUX compiler (zig/src/capi.zig).
 *
 * Text functions take a UTF-8 CRUX source buffer and return
 *   0  artifact in *out
 *   1  diagnostic "file:line:col: error: ..." in *out
 *   2  allocation failure, *out == NULL
 * Every non-NULL *out must be released with crux_free. */
#ifndef CRUX_H
#define CRUX_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

const char *crux_version(void);
void crux_free(char *p);

int crux_lex(const char *src, size_t len, char **out);
int crux_parse(const char *src, size_t len, char **out);
int crux_lower(const char *src, size_t len, char **out);
int crux_emit_smt(const char *src, size_t len, char **out);
int crux_emit_lean(const char *src, size_t len, char **out);
int crux_emit_sas(const char *src, size_t len, char **out);
int crux_emit_cuda(const char *src, size_t len, char **out);
int crux_cert(const char *src, size_t len, char **out);
int crux_check(const char *src, size_t len, char **out);
int crux_run(const char *src, size_t len, char **out);
int crux_solve(const char *src, size_t len, char **out);

/* Abjad matrix. */
int crux_abjad_value(const char *text, size_t len, uint32_t *value);
uint8_t crux_abjad_digit_root(uint32_t n);
uint32_t crux_abjad_letter_value(int index);
bool crux_wafq_allah_verify(void);
void crux_wafq_allah_sums(uint32_t out[8]);

#ifdef __cplusplus
}
#endif

#endif /* CRUX_H */
