# A 128 bound with unrestricted ambient nilpotency class

The proof in `RibbonDerived3Family.lean` applies to the single-matching bi-Cayley graph whose two rims have generators x and y. For a finite nilpotent group of order coprime to 6 and with commutator subgroup of nilpotency class at most three, every nonidentity x and y give a simple cycle of length 4, 8, 16, 32, 64, or 128. It does not assume that the two rim generators generate the ambient group. It is not the unrestricted Erdős–Gyárfás conjecture, nor does it extend the characteristic-three branches.

The core algebra removes the ambient class-eight condition from four words used by the preceding certificates. Put D=[G,G]. In each word U is in D, and R is in [D,D] by its exact conjugacy to a double commutator. Thus Z is in γ₃(D), so Z commutes with U if γ₄(D)=1. This proves the same length-128 closure, while pairwise vertex separation is still controlled by the same checked class-two and class-three charts. The local large projected order theorem needs no ambient nilpotence. The generated-subgroup descents at projected orders 1, 5, and 7 use eventual ambient nilpotence, with no fixed bound.

Replay with `bash replay-local.sh /path/to/built/mathlib4`. Final handles: `RibbonDerived3.local_bound`, `RibbonDerived3.projected_order_5_or_7`, and `RibbonDerived3.odd_not_three`. The three files use only standard axioms.
