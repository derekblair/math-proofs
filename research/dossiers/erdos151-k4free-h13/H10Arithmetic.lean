import Lean.Elab.Tactic.Omega

namespace Erdős151.H12

theorem h10_exclude_ambient_nine (n r I l : Nat)
    (hn : 36 ≤ n) (hr : 8 ≤ r)
    (hlo : 12*(n-10) ≤ 4*I+54+2*l)
    (hi : I+2*r ≤ 72) (hl : l+7*r ≤ 72) : False := by omega

theorem h10_exclude_ambient_eight (n I : Nat) (hn : 36 ≤ n)
    (hlo : 6*(n-12) ≤ 2*I+40) (hi : I ≤ 48) : False := by omega

theorem core_density_excludes_n55 (V E T L : Nat)
    (hv : 1 ≤ V) (hhandshake : 2*E=8*V)
    (hlinksum : L=3*T) (hlocal : L≤11*V) (hdens : E≤T) : False := by omega

theorem two_hub_lower (n du dv c xu xv q : Nat)
    (hq : q+2+c+xu+xv=du+dv) (cannot_insert : n-42 ≤ q) (hn : 42 ≤ n) :
    n-40+c+xu+xv ≤ du+dv := by omega

#print axioms h10_exclude_ambient_nine
#print axioms h10_exclude_ambient_eight
#print axioms core_density_excludes_n55
#print axioms two_hub_lower
end Erdős151.H12
