# IrisHoles ledger

Every assumption left in the Iris route is a field of `structure IrisHoles` and has a row here. `scripts/check_iris_holes.py` checks the two agree. A hole is discharged by proving the field and deleting both the field and its row in the same commit.

| field | what it assumes | owner | satisfiability evidence | discharge plan |
|---|---|---|---|---|
| `newlib.snprintf` | `snprintf(dst, n, fmt, a3…a7)` with `0 < n < 2^31` and a `%s`/`%d` format (`FmtArgsOK`) writes a NUL-terminated string into `dst[0,n)`, keeps `stdioOwn`, prints nothing, returns with the ABI frame, in 1024 bytes of stack (`Newlib.snprintfSpec`) | H5; scheduled after E1–E6 (user, Q4) | `%lld` success path proved (VSA M3, `SnprintfSpec*`); measured frames 272 + 592 + 64 | M3 format-parser and digit-loop segments; `%s` copy loop |
| `out.snprintfFn` | `snprintf(buf, 64, "<fn %s>", name)` leaves `("<fn " ++ name ++ ">")` cut to 63 characters and a NUL in `buf` (`NewlibOut.snprintfFnSpec`), keeps `stdioOwn`, prints nothing, in `snprintfNeed` (1024) bytes | H2 hole, scheduled with the newlib holes (Q4) | `%s` copy into a string `FILE` (`__ssputs_r`), M3's format parser; C99 7.19.6.5 truncation | M3 parser segments + the `%s` copy loop (shared with `newlib.snprintf`) |
| `out.snprintfInt` | `snprintf(buf, 64, "%lld", i)` leaves `intToString i` and a NUL in `buf` (`NewlibOut.snprintfIntSpec`), keeps `stdioOwn`, prints nothing, in `snprintfNeed` (1024) bytes | H2 hole, scheduled with the newlib holes (Q4) | VSA M3 proved the `%lld` success path (`SnprintfSpec*`); at most 20 characters, never cut | M3's format parser and digit loop, as segments (shared with `newlib.snprintf`) |
