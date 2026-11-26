# Field certificate generators

Use Python and SymPy in a scratch copy. Inputs are frozen exact selections:
`candidates-frozen.tsv`, `all_forms.log`, `cover145.fast.log` and
`residual-frozen.log`. Keep the supplied slope-selection log, which
includes the table-capacity adjustments and the direct F43 branch.

Run these in order as Python scripts: `gen_words.py`, `gen_symbols.py`,
`gen_surface_odd.py`, `gen_slope_certs.py`, `gen_mod_leaves.py`,
`gen_slope_lean.py`, `gen_mod_lean.py`, `gen_extras_lean.py`.
The surface generator is independent of the slope selection and output.
Lean checks the generated geometry and all integer/modular identities, so
none of these Python programs is trusted by the proof.
