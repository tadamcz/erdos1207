# Provenance

`SHA256SUMS` records the SHA-256 of the file the benchmark harness captured: 632,950 bytes, a submission artifact of
the sample `Erdos1207.erdos_1207` in the eval set `erdos-ultima-alpha-1000usd` (sample uuid
`cTsYA4Q65LmZ9kjKMAWq6d`, 3-5 September 2026). It is the model's own file, unedited.

`Solution.diff` is the unified diff from that artifact to `Solution.lean`. It consists only of the `import` line and
the vendored Formal Conjectures definitions, both listed in the README. Reversing it reproduces the artifact bit for
bit, which CI checks against the hash above.
