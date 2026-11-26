import FiniteTripTrace

namespace NeutralDecider
open FiniteTrip FiniteTripTrace TripTrace AffineAddress CutLift PhaseProduct

variable (D : Finset ℤ) (f : ℤ → List ℤ)
variable (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)
variable (A : (ℤ×ℤ) →+ (ℤ×ℤ))
variable (aff : ∀ x ∈ D, σ (f x)=A (σ [x]))
variable (u v : ℤ×ℤ) (m : ℤ) (neg : Bool)
variable (a : ℤ) (ha : a∈D)

def limit : ℤ := ∑ i : Edge D f, |NeutralTrace.pro v (stamp D f i)|

theorem limit_nonneg : 0 ≤ limit D f v :=
  Finset.sum_nonneg fun _i _ => abs_nonneg _

theorem limit_bounds (i : Edge D f) :
    |NeutralTrace.pro v (stamp D f i)| ≤ limit D f v :=
  Finset.single_le_sum (f := fun i : Edge D f => |NeutralTrace.pro v (stamp D f i)|)
    (fun _j _ => abs_nonneg _) (Finset.mem_univ i)

theorem limit_zero : (0 : ℤ) ∈ IntegerTrace.box (limit D f v) := by
  rw [IntegerTrace.box_iff,abs_zero]
  exact limit_nonneg D f v

def strict (x : State D) : Prop := x.2.2.2.1 = true ∧ x.2.2.2.2 = true

instance (x : State D) : Decidable (strict D x) := by unfold strict; infer_instance

theorem strict_real {w : List ℤ} (T : Triple w) (h : ∀ z ∈ w, z∈D) :
    strict D (restrictShape D T h) ↔ idx T.a < idx T.b ∧ idx T.b < idx T.c := by
  simp [strict,restrictShape,CutOrder.shape]

def decides : Bool :=
  let M := machine D f closed u v m neg
  decide (∃ y : State D, strict D y ∧
    PhaseFinite.accept M (limit D f v) (vertex D f closed a ha (n:=0) (root a))
      y (limit_zero D f v)=true)

include aff in
theorem decides_iff
    (eU : ∀ p, NeutralTrace.pro u (A p) = sign neg * NeutralTrace.pro u p)
    (eV : ∀ p, NeutralTrace.pro v (A p) = m * NeutralTrace.pro v p)
    (hm : 1 < |m|) (hUV : u.1*v.2-u.2*v.1 ≠ 0) :
    decides D f closed u v m neg a ha = true ↔
    ∃ (n : ℕ) (x y z t : List ℤ), iter f a n = x++y++z++t ∧
      0 < y.length ∧ y.length=z.length ∧ y.sum=z.sum ∧ t ≠ [] := by
  let M := machine D f closed u v m neg
  have e : ∀ y : State D, PhaseFinite.accept M (limit D f v)
      (vertex D f closed a ha (n:=0) (root a)) y (limit_zero D f v)=true ↔
      ∃ L, Path M (vertex D f closed a ha (n:=0) (root a)) y L ∧
        NeutralTrace.run A 0 (L.map (stamp D f))=0 := by
    intro y
    have hsafe : limit D f v ≤ (|m|-1)*limit D f v := by
      have hh : 1 ≤ |m|-1 := by omega
      simpa using mul_le_mul_of_nonneg_right hh (limit_nonneg D f v)
    rw [PhaseFinite.accept_iff M _ _ _ _ (limit D f v) (limit_bounds D f v)
      hm (limit_nonneg D f v) hsafe]
    apply exists_congr
    intro L
    apply and_congr_right
    intro _
    have hu := NeutralTrace.proj_run A u (sign neg) eU (0,0) (L.map (stamp D f))
    have hv := NeutralTrace.proj_run A v m eV (0,0) (L.map (stamp D f))
    simp only [List.map_map,Function.comp_def,NeutralTrace.pro,mul_zero,add_zero] at hu hv
    change ScalarTrace.zeval m 0 (L.map fun i => NeutralTrace.pro v (stamp D f i)) = 0 ∧
      ScalarTrace.zeval (sign neg) 0 (L.map fun i => NeutralTrace.pro u (stamp D f i)) = 0 ↔ _
    constructor
    · rintro ⟨hv0,hu0⟩
      have hu' : NeutralTrace.pro u (NeutralTrace.run A 0 (L.map (stamp D f)))=0 := hu.trans hu0
      have hv' : NeutralTrace.pro v (NeutralTrace.run A 0 (L.map (stamp D f)))=0 := hv.trans hv0
      obtain ⟨h1,h2⟩ := NeutralAffine.projections_zero _ _ _ _ _ _ hUV hu' hv'
      exact Prod.ext h1 h2
    · intro hz
      change NeutralTrace.run A (0,0) (L.map (stamp D f)) = (0,0) at hz
      rw [hz] at hu hv
      exact ⟨by simpa [NeutralTrace.pro] using hv.symm,
        by simpa [NeutralTrace.pro] using hu.symm⟩
  change decide (∃ y, strict D y ∧ PhaseFinite.accept M _ _ y _=true)=true ↔ _
  simp only [decide_eq_true_eq,e]
  constructor
  · rintro ⟨y,hy,L,hL,hzero⟩
    obtain ⟨n,T,ht,he,hΔ⟩ := realizes D f closed A aff u v m neg a ha (n:=0)
      (root a) (root_ordered a) hL rfl
    change delta T = NeutralTrace.run A 0 (L.map (stamp D f)) at hΔ
    rw [hzero] at hΔ
    rw [he] at hy
    obtain ⟨hx,hy⟩ := (strict_real D T _).mp hy
    obtain ⟨x,y,z,t,h,hx,hy,hz,ht⟩ := actual_square T hx hy hΔ
    exact ⟨n,x,y,z,t,h,hx,hy,hz,ht⟩
  · rintro ⟨n,x,y,z,t,h,hx,hy,hz,ht⟩
    obtain ⟨T,h1,h2,hΔ⟩ := from_square x y z t h hx hy hz ht
    obtain ⟨L,hL,hVal⟩ := from_triple D f closed A aff u v m neg a ha T ⟨h1.le,h2.le⟩
    exact ⟨_,(strict_real D T _).mpr ⟨h1,h2⟩,L,hL,hVal.symm.trans hΔ⟩

end NeutralDecider

#print axioms NeutralDecider.decides_iff
