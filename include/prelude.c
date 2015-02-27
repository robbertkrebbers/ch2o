/* Copyright (c) 2012-2015, Freek Wiedijk and Robbert Krebbers. */
/* This file is distributed under the terms of the BSD license. */
/** Helpers for the emulation of printf that compute the length of a printed
    string */

int __ch2o_len_core(int n, unsigned long long i, int w) {
  if (i == 0) { n = 1; }
  while (0 < i) { n++; i /= 10; }
  return n < w ? w : n;
}

int __ch2o_len_core_signed(int n, long long i, int w) {
  if (0 <= i) {
    return __ch2o_len_core(n,i,w);
  } else if (i == __ch2o_builtin_min((long long)0)) {
    return __ch2o_len_core(n,i,w);
  } else {
    return __ch2o_len_core(n,i * -1,w);
  }
}

int __ch2o_len_core_string(int n, char *p, int w) {
  while (*p) { n++; p++; }
  return n < w ? w : n;
}
