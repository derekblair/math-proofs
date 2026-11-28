import N62SimpleOwner

namespace Erdos151N62
open Erdős151.Upper Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : V→V→Prop) [DecidableRel E]

/-- An unoriented edge with at least one endpoint in Z consumes one
slot from the degree sum over Z. This directed bound accounts for
each such edge twice and avoids assumptions about other vertices. -/
theorem split_directed_at
    (sym : ∀ {a b}, E a b → E b a) (T Z : Finset V) (zt : Z⊆T)
    (lo : ∀ u∈Z, row E T u≤3)
    (hi : ∀ u∈T\Z, row E (T\Z) u≤2)
    (W : Finset V) (ws : W⊆T\Z)
    (zero : ∀ u∈(T\Z)\W, row E (T\Z) u=0) :
    (∑ u∈T,row E T u)≤6*Z.card+2*W.card := by
  classical
  let R := T\Z
  have e : Z∪R=T := union_sdiff_of_subset zt
  have dis : Disjoint Z R := disjoint_sdiff
  have rSplit (u : V) : row E T u=row E Z u+row E R u := by
    have e' : T.filter (E u)=(Z.filter (E u))∪(R.filter (E u)) := by
      rw [←e,filter_union]
    change (T.filter (E u)).card=(Z.filter (E u)).card+(R.filter (E u)).card
    rw [e',card_union_of_disjoint ((dis.mono_left (filter_subset _ _)).mono_right (filter_subset _ _))]
  have tsym (u v : V) : E u v ↔ E v u := ⟨sym,sym⟩
  have cross : (∑ u∈R,row E Z u)=∑ u∈Z,row E R u := by
    have q := transpose E Z R
    unfold incidence at q
    have f (u : V) : (Z.filter (fun v=>E v u)).card=row E Z u := by
      congr 1
      apply filter_congr
      intro v hv
      exact tsym v u
    simpa only [f] using q
  have zsum : (∑ u∈Z,row E T u)≤3*Z.card := by
    have q := sum_le_sum lo
    simpa [Nat.mul_comm] using q
  have zr : (∑ u∈Z,row E R u)≤∑ u∈Z,row E T u := by
    apply sum_le_sum
    intro u hu
    rw [rSplit]
    omega
  have rhi : (∑ u∈R,row E R u)≤2*W.card := by
    have hl : (∑ u∈W,row E R u)≤2*W.card := by
      have q := sum_le_sum (fun u hu=>hi u (ws hu))
      simpa [Nat.mul_comm] using q
    have z0 : (∑ u∈R\W,row E R u)=0 := sum_eq_zero (fun u hu=>zero u hu)
    have q := sum_sdiff ws (f:=row E R)
    change (∑ u∈R\W,row E R u)+(∑ u∈W,row E R u)=(∑ u∈R,row E R u) at q
    omega
  have q := sum_sdiff zt (f:=row E T)
  change (∑ u∈R,row E T u)+(∑ u∈Z,row E T u)=_ at q
  have rsum : (∑ u∈R,row E T u)=(∑ u∈R,row E Z u)+(∑ u∈R,row E R u) := by
    rw [←sum_add_distrib]
    exact sum_congr rfl (fun u _=>rSplit u)
  omega

#print axioms split_directed_at
end Erdos151N62
