# Untrusted certificate generation

Run in a scratch copy of this directory with Python and SymPy:
1. `python all_forms.py > all_forms.log`, `python gen_words.py`, `python gen_symbols.py`.
2. `python gen_base145.py`, `python gen_surface_lean.py`.
3. `python cover.py > cover145.fast.log`, then run `gen_slope_certs.py`, `gen_slope_mod.py`, `gen_mod_leaves.py`, `gen_slope_lean.py`, `gen_mod_lean.py` and `gen_pack_final.py` with Python in that order.

The frozen original corpus contains 904 candidate words. The Lean sources are already checked without running any of these programs. Each stored word identity and polynomial identity is checked against its actual statement.
