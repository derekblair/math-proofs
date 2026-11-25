import Pack
import Mathlib.Data.Fintype.EquivFin

namespace CoverCutoff

/-- Three residue columns, with a single late B entry between the first two A entries. -/
def familyRank (h pos : ℕ) : ℕ :=
  let q := pos/3
  match pos%3 with
  | 0 => if q=0 then h-1 else h+q
  | 1 => if q=h-1 then h else q
  | _ => 2*h+1+q

lemma familyRank_A0 {h : ℕ} : familyRank h 0=h-1 := by simp [familyRank]

lemma familyRank_A {h q : ℕ} (hq : 0<q) : familyRank h (3*q)=h+q := by
  have hh : 3*q/3=q := by omega
  have hm : (3*q)%3=0 := by omega
  simp [familyRank,hm,hh,ne_of_gt hq]

lemma familyRank_B {h q : ℕ} :
    familyRank h (3*q+1)=(if q=h-1 then h else q) := by
  have hh : (3*q+1)/3=q := by omega
  have hm : (3*q+1)%3=1 := by omega
  simp [familyRank,hm,hh]

lemma familyRank_C {h q : ℕ} : familyRank h (3*q+2)=2*h+1+q := by
  have hh : (3*q+2)/3=q := by omega
  have hm : (3*q+2)%3=2 := by omega
  simp [familyRank,hm,hh]

lemma familyRank_bound {h pos : ℕ} (hh : 2≤h) (hp : pos<3*h+1) :
    familyRank h pos<3*h+1 := by
  have hm : pos%3=0 ∨ pos%3=1 ∨ pos%3=2 := by omega
  rcases hm with hv|hv|hv
  · simp [familyRank,hv]
    split <;> omega
  · simp [familyRank,hv]
    split <;> omega
  · simpa [familyRank,hv] using (show 2*h+1+pos/3<3*h+1 by omega)

lemma familyRank_inj {h x y : ℕ} (hh : 2≤h) (hx : x<3*h+1)
    (hy : y<3*h+1) (he : familyRank h x=familyRank h y) : x=y := by
  have hm₁ : x%3=0 ∨ x%3=1 ∨ x%3=2 := by omega
  have hm₂ : y%3=0 ∨ y%3=1 ∨ y%3=2 := by omega
  obtain ha|ha|ha := hm₁ <;> obtain hb|hb|hb := hm₂ <;>
    simp only [familyRank,ha,hb] at he <;>
    first | split_ifs at he <;> omega | omega

noncomputable def delayed (h : ℕ) (hh : 2≤h) : Equiv.Perm (Fin (3*h+1)) :=
  Equiv.ofBijective (fun x => ⟨familyRank h x.val,familyRank_bound hh x.isLt⟩)
    ((Finite.injective_iff_bijective).mp (fun x y hxy => Fin.ext
      (familyRank_inj hh x.isLt y.isLt (congrArg Fin.val hxy))))

@[simp] lemma delayed_val (h : ℕ) (hh : 2≤h) (i : Fin (3*h+1)) :
    (delayed h hh i).val=familyRank h i.val := rfl

#print axioms delayed
end CoverCutoff
