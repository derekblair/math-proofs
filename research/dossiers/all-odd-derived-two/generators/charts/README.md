# Finite chart certificate generators

Run with Python in a scratch copy, in this order:
`gen_all_odd_finite.py`, `tables.py`, `gen_pair_bank.py`,
`gen_jet_sort.py`, `gen_projected_cert.py`.
The literal chart keys are verified against certified word walks. The
sorted certificates check an inverse rank lookup and each adjacent key
and owner, not an assumed correctness of Python sorting or arithmetic.
Only the proof sources listed in the replay order are used.
