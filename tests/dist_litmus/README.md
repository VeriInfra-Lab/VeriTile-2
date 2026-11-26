# Litmus sources of the Dist line

One file per row of [the litmus table](../../documents/dist/LitmusTable.md),
named by the row ID. Each file is the program of its row in the front-end
language the example comes from: Triton-distributed at `7908e4e` or TileScale
at `71e7145` (a07–a10, b09, b11, b12 and c09).
The first three comment lines record the pinned source paths and lines, the
SPDX licence expression and the changes. The row ID, context and launch
assumptions follow. [Third-party notices](../../THIRD_PARTY_NOTICES.md)

These source files serve the tickets that run the rows on the event model
and on the GPU. `python3 scripts/check_docs.py` checks their attribution;
`python3 -m py_compile tests/dist_litmus/*.py` checks their Python syntax.
