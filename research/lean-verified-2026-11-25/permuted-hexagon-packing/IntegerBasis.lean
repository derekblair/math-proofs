import Mathlib.Tactic
import Mathlib.Data.Int.ModEq

namespace PermHex

def PrimitiveRow (a b : ℤ) : Prop := ∃ x y : ℤ, a*x+b*y=1

def det (a b c d : ℤ) : ℤ := a*d-b*c

lemma positive_natCast {N : ℤ} (hN : 0<N) : (N.toNat:ℤ)=N :=
  Int.toNat_of_nonneg hN.le

def remval (N m x : ℤ) : ℤ := (m*x) % N

lemma inverse_mod {N m u v x : ℤ} (hu : u*m=1+N*v) :
    (u*remval N m x)%N=x%N := by
  have h0 := Int.emod_add_mul_ediv (m*x) N
  change remval N m x + N * (m*x/N)=m*x at h0
  have he : u*remval N m x-x=N*(v*x-u*(m*x/N)) := by
    linear_combination u*h0 + x*hu
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-(v*x-u*(m*x/N)),?_⟩
  linear_combination -he

lemma remval_lt {N : ℤ} (hN : 0<N) (m x : ℤ) :
    (remval N m x).toNat<N.toNat :=
  (Int.toNat_lt_toNat hN).mpr (Int.emod_lt_of_pos _ hN)

noncomputable def residuePerm {N m u v : ℤ} (hN : 0<N) (hu : u*m=1+N*v) :
    Equiv.Perm (Fin N.toNat) :=
  Equiv.ofBijective (fun x => ⟨(remval N m x.val).toNat,remval_lt hN m x.val⟩)
    (Finite.injective_iff_bijective.mp (by
      intro x y hxy
      have hx0 : 0≤remval N m x.val := Int.emod_nonneg _ (ne_of_gt hN)
      have hy0 : 0≤remval N m y.val := Int.emod_nonneg _ (ne_of_gt hN)
      have hr := congrArg Fin.val hxy
      change (remval N m x.val).toNat=(remval N m y.val).toNat at hr
      have hr' := congrArg (fun n : ℕ => (n:ℤ)) hr
      rw [Int.toNat_of_nonneg hx0,Int.toNat_of_nonneg hy0] at hr'
      have hx : (x.val:ℤ)<(N.toNat:ℤ) := by exact_mod_cast x.isLt
      have hy : (y.val:ℤ)<(N.toNat:ℤ) := by exact_mod_cast y.isLt
      rw [positive_natCast hN] at hx hy
      have hx' := Int.emod_eq_of_lt (by positivity) hx
      have hy' := Int.emod_eq_of_lt (by positivity) hy
      have he := inverse_mod (x:=x.val) hu
      rw [hr',inverse_mod hu,hx',hy'] at he
      exact Fin.ext (by exact_mod_cast he.symm)))

lemma residue_finVal {N m u v : ℤ} (hN : 0<N) (hu : u*m=1+N*v) (i : Fin N.toNat) :
    ((residuePerm hN hu i).val:ℤ)=remval N m i.val :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hN))

/-- Restrict the integer lattice to one representative per row and column. -/
theorem primitive_lattice_permutation {a b c d : ℤ}
    (hN : 0<det a b c d) (hA : PrimitiveRow a b) (hB : PrimitiveRow c d) :
    ∃ p : Equiv.Perm (Fin (det a b c d).toNat), ∀ i j,
      ∃ x y : ℤ, (i.val:ℤ)-j.val = a*x+b*y ∧ ((p i).val:ℤ)-(p j).val = c*x+d*y := by
  obtain ⟨p,q,hp⟩ := hA
  obtain ⟨r,s,hr⟩ := hB
  let m := c*p+d*q
  let N := det a b c d
  let u := a*r+b*s
  have ham : a*m-c=q*N := by dsimp [m,N,det]; linear_combination c*hp
  have hbm : b*m-d= -p*N := by dsimp [m,N,det]; linear_combination d*hp
  have hu : u*m=1+N*(q*r-p*s) := by
    dsimp [u]
    linear_combination r*ham+s*hbm+hr
  let M := residuePerm hN hu
  refine ⟨M,?_⟩
  intro i j
  let X : ℤ := (i.val:ℤ)-j.val
  let h := (m*(i.val:ℤ)/N)-(m*(j.val:ℤ)/N)
  have he : remval N m i.val-remval N m j.val = m*X-N*h := by
    have hi := Int.emod_add_mul_ediv (m*(i.val:ℤ)) N
    have hj := Int.emod_add_mul_ediv (m*(j.val:ℤ)) N
    change remval N m i.val+N*(m*(i.val:ℤ)/N)=m*(i.val:ℤ) at hi
    change remval N m j.val+N*(m*(j.val:ℤ)/N)=m*(j.val:ℤ) at hj
    dsimp [X,h]
    linear_combination hi-hj
  refine ⟨p*X+b*h,q*X-a*h,?_,?_⟩
  · change X = _
    linear_combination -X*hp
  · change ((residuePerm hN hu i).val:ℤ)-(residuePerm hN hu j).val=_
    rw [residue_finVal,residue_finVal,he]
    dsimp [m,N,det]
    ring

#print axioms primitive_lattice_permutation
end PermHex
