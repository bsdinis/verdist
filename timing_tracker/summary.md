# 0007: 2026-09-12 11:04:34

- overhauled profile_proof.sh/print_profile_stats.sh: single verify pass (was 2), jq -s stream fix for multi-crate --output-json output, explicit -p abd default with cargo clean -p to dodge cargo's content-hash fingerprint cache, auto-appended summary.md entry, regression check

|                                     |                                          |
|---|---|
|                             package |                                   abd    |
|                             profile |                               release    |
|                             version |            0.2026.09.11.307b4d5.dirty    |
|                            platform |                          linux_x86_64    |
|                           toolchain |       1.98.1-x86_64-unknown-linux-gnu    |
|                         (overridden |                                    by    |
|                         environment |                              variable    |
|                   RUSTUP_TOOLCHAIN) |                                          |
|                        verus commit | 307b4d57eabbff063dc5fa432b026509276ef292 |
|                            hostname |                        verdist-387b3f    |
|                           n_threads |                                    15    |
|                            verified |                                   346    |
|                  total (wall-clock) |                                  4831 ms |
|                         total (cpu) |                                 12929 ms |
|           verification (wall-clock) |                                  2951 ms |
|                  verification (cpu) |                                  9414 ms |
|                       smt run (cpu) |                                  3428 ms |
|                              client |                                  1219 ms |
|              client::net_invs::read |                                   981 ms |
|               invariants::lin_queue |                                   848 ms |
|              invariants::quorum::lb |                                   642 ms |
|                    server::lockfree |                                   550 ms |
|                  elapsed wall clock |                               0:05.79    |

---

# 0006: 2025-12-26 09:56:08

- manually selected triggers

even though most triggers were the automatically chosen, this seems to have helped

|                                     |                                          |
|---|---|
|                             profile |                               release    |
|                             version |            0.2025.12.22.95ec04c.dirty    |
|                            platform |                          linux_x86_64    |
|                           toolchain |       1.91.0-x86_64-unknown-linux-gnu    |
|                        verus commit | 95ec04c1198741329100b84cae4c3b49916b1c52 |
|                            hostname |                                bertha    |
|                           n_threads |                                    15    |
|                  total (wall-clock) |                                  2996 ms |
|                         total (cpu) |                                  8242 ms |
|           verification (wall-clock) |                                  1856 ms |
|                  verification (cpu) |                                  6266 ms |
|                       smt run (cpu) |                                  1569 ms |
|          abd::invariants::lin_queue |                                   921 ms |
|                         abd::client |                                   806 ms |
|             abd::invariants::quorum |                                   426 ms |
|       abd::invariants::committed_to |                                   375 ms |
|                                     |                                   366 ms |
|                  elapsed wall clock |                               0:03.68    |

---

# 0005: 2025-12-26 07:52:09

- moved Pending and Committed to use type_invariant

|                                     |                                          |
|---|---|
|                             profile |                               release    |
|                             version |            0.2025.12.22.95ec04c.dirty    |
|                            platform |                          linux_x86_64    |
|                           toolchain |       1.91.0-x86_64-unknown-linux-gnu    |
|                        verus commit | 95ec04c1198741329100b84cae4c3b49916b1c52 |
|                            hostname |                                bertha    |
|                           n_threads |                                    15    |
|                  total (wall-clock) |                                  4395 ms |
|                         total (cpu) |                                 10322 ms |
|           verification (wall-clock) |                                  2627 ms |
|                  verification (cpu) |                                  7165 ms |
|                       smt run (cpu) |                                  1956 ms |
|          abd::invariants::lin_queue |                                  1122 ms |
|                         abd::client |                                  1019 ms |
|             abd::invariants::quorum |                                   470 ms |
|                                     |                                   421 ms |
|       abd::invariants::committed_to |                                   404 ms |
|                 ellapsed wall clock |                               0:04.92    |

---

# 0004: 2025-12-26 07:27:30

- closed up LinearizationQueue

probable regression -- maybe leaning more on lemmas would be good

|                                     |                                          |
|---|---|
|                             profile |                               release    |
|                             version |            0.2025.12.22.95ec04c.dirty    |
|                            platform |                          linux_x86_64    |
|                           toolchain |       1.91.0-x86_64-unknown-linux-gnu    |
|                        verus commit | 95ec04c1198741329100b84cae4c3b49916b1c52 |
|                            hostname |                                bertha    |
|                           n_threads |                                    15    |
|                  total (wall-clock) |                                  4463 ms |
|                         total (cpu) |                                 10414 ms |
|           verification (wall-clock) |                                  2669 ms |
|                  verification (cpu) |                                  7263 ms |
|                       smt run (cpu) |                                  2000 ms |
|          abd::invariants::lin_queue |                                  1212 ms |
|                         abd::client |                                  1026 ms |
|             abd::invariants::quorum |                                   488 ms |
|       abd::invariants::committed_to |                                   427 ms |
|                                     |                                   416 ms |
|                 ellapsed wall clock |                               0:04.98    |

---

# 0003: 2025-12-25 21:49:39

- closed up Pending and Committed

|                                     |                                          |
|---|---|
|                             profile |                               release    |
|                             version |            0.2025.12.22.95ec04c.dirty    |
|                            platform |                          linux_x86_64    |
|                           toolchain |       1.91.0-x86_64-unknown-linux-gnu    |
|                        verus commit | 95ec04c1198741329100b84cae4c3b49916b1c52 |
|                            hostname |                                bertha    |
|                           n_threads |                                    15    |
|                  total (wall-clock) |                                  3099 ms |
|                         total (cpu) |                                  8641 ms |
|           verification (wall-clock) |                                  1990 ms |
|                  verification (cpu) |                                  6706 ms |
|                       smt run (cpu) |                                  1824 ms |
|                         abd::client |                                  1088 ms |
|          abd::invariants::lin_queue |                                   877 ms |
|             abd::invariants::quorum |                                   447 ms |
|                                     |                                   412 ms |
|       abd::invariants::committed_to |                                   380 ms |
|                 ellapsed wall clock |                               0:05.44    |

---

# 0002: 2025-12-24 22:11:08

- closed up committed to

|                                     |                                          |
|---|---|
|                             profile |                               release    |
|                             version |            0.2025.12.22.95ec04c.dirty    |
|                            platform |                          linux_x86_64    |
|                           toolchain |       1.91.0-x86_64-unknown-linux-gnu    |
|                        verus commit | 95ec04c1198741329100b84cae4c3b49916b1c52 |
|                            hostname |                                bertha    |
|                           n_threads |                                    15    |
|                  total (wall-clock) |                                  3214 ms |
|                         total (cpu) |                                  8822 ms |
|           verification (wall-clock) |                                  2098 ms |
|                  verification (cpu) |                                  6870 ms |
|                       smt run (cpu) |                                  1890 ms |
|                         abd::client |                                  1176 ms |
|          abd::invariants::lin_queue |                                   944 ms |
|             abd::invariants::quorum |                                   453 ms |
|                                     |                                   428 ms |
|       abd::invariants::committed_to |                                   394 ms |
|                  elapsed wall clock |                               0:04.15    |

---

# 0001: 2025-12-24 22:11:08

- initial benchmarking

|                                     |                                          |
|---|---|
|                             profile |                               release    |
|                             version |            0.2025.12.22.95ec04c.dirty    |
|                            platform |                          linux_x86_64    |
|                           toolchain |       1.91.0-x86_64-unknown-linux-gnu    |
|                        verus commit | 95ec04c1198741329100b84cae4c3b49916b1c52 |
|                            hostname |                                bertha    |
|                           n_threads |                                    15    |
|                  total (wall-clock) |                                  3298 ms |
|                         total (cpu) |                                  8936 ms |
|           verification (wall-clock) |                                  2207 ms |
|                  verification (cpu) |                                  7038 ms |
|                       smt run (cpu) |                                  2104 ms |
|                         abd::client |                                  1339 ms |
|          abd::invariants::lin_queue |                                   995 ms |
|             abd::invariants::quorum |                                   444 ms |
|                                     |                                   421 ms |
|       abd::invariants::committed_to |                                   351 ms |
|                  elapsed wall clock |                               0:04.15    |
