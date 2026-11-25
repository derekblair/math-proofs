import Statement
import Mathlib.Tactic

namespace FibPopularity
open Emerging

def Far (n : Nat) (f : Perm n) : Prop :=
  ∀ i j : Nat, j < n → i+2 ≤ j → ext f i < ext f j

noncomputable def forbidden4 : Finset (Perm 4) := by
  classical
  exact Finset.univ.filter (fun p => ∃ r s : Fin 4, r.val+2 ≤ s.val ∧ p s < p r)

theorem far_avoids (n : Nat) (f : Perm n) (hf : Far n f) : avoids f forbidden4 := by
  classical
  intro p hp i hi
  obtain ⟨a,b,hab,hp'⟩ := (Finset.mem_filter.mp hp).2
  have hi' := i.isLt
  have hb := b.isLt
  have hh := hf (i.val+a.val) (i.val+b.val) (by omega) (by omega)
  exact (not_lt_of_gt hp') ((hi a b).mp hh)

theorem avoids_local (n : Nat) (hn : 4 ≤ n) (f : Perm n) (hf : avoids f forbidden4)
    (i j : Nat) (hj : j < n) (hlo : i+2 ≤ j) (hhi : j ≤ i+3) :
    ext f i < ext f j := by
  classical
  let l := min i (n-4)
  have hs : l ≤ i ∧ j < l+4 ∧ l+4 ≤ n := by
    simp only [l,Nat.min_def]; split <;> omega
  obtain ⟨p,hp⟩ := occurs_exists n 4 f l hs.2.2
  let a : Fin 4 := ⟨i-l,by omega⟩
  let b : Fin 4 := ⟨j-l,by omega⟩
  have hh : p ∉ forbidden4 := fun h => hf p h ⟨l,by omega⟩ hp
  have hcmp : p a < p b := by
    rcases lt_trichotomy (p a) (p b) with hpab|heq|hpba
    · exact hpab
    · have hE := congrArg Fin.val (p.injective heq)
      dsimp [a,b] at hE
      omega
    · exfalso
      apply hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,b,by dsimp [a,b]; omega,hpba⟩
  have h1 : l+a.val=i := by dsimp [a]; omega
  have h2 : l+b.val=j := by dsimp [b]; omega
  have ht := (hp a b).mpr hcmp
  rwa [h1,h2] at ht

theorem avoids_far (n : Nat) (hn : 4 ≤ n) (f : Perm n) (hf : avoids f forbidden4) : Far n f := by
  intro i j hj hlo
  have aux (d : Nat) : ∀ a, a+d<n → 2≤d → ext f a < ext f (a+d) := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro a ha hd
      by_cases h3 : d≤3
      · exact avoids_local n hn f hf a (a+d) ha (by omega) (by omega)
      · have hl := avoids_local n hn f hf a (a+2) (by omega) (by omega) (by omega)
        have hr := ih (d-2) (by omega) (a+2) (by omega) (by omega)
        rw [show a+2+(d-2)=a+d by omega] at hr
        exact hl.trans hr
  have hh := aux (j-i) i (by omega) (by omega)
  rwa [show i+(j-i)=j by omega] at hh

def Valid (n : Nat) (f : Fin n → Bool) : Prop :=
  (∀ i : Fin n, f i = true → i.val+1 < n) ∧
  (∀ i j : Fin n, i.val+1=j.val → f i = true → f j = false)
abbrev Mask (n : Nat) := {f : Fin n → Bool // Valid n f}

def bit {n : Nat} (s : Mask n) (i : Nat) : Bool := if h : i<n then s.val ⟨i,h⟩ else false

theorem bit_fin {n : Nat} (s : Mask n) (i : Fin n) : bit s i.val = s.val i := by simp [bit,i.isLt]

theorem bit_true_lt {n i : Nat} (s : Mask n) (hi : bit s i = true) : i+1<n := by
  unfold bit at hi
  split at hi
  next h => exact s.property.1 ⟨i,h⟩ hi
  next => cases hi

theorem bits_disjoint {n i : Nat} (s : Mask n) (hi : bit s i = true) : bit s (i+1)=false := by
  have h1 := bit_true_lt s hi
  have h0 : i<n := by omega
  have h0' : s.val ⟨i,h0⟩=true := by simpa [bit,h0] using hi
  simpa [bit,h1] using s.property.2 ⟨i,h0⟩ ⟨i+1,h1⟩ rfl h0'

def sw {n : Nat} (s : Mask n) (i : Nat) : Nat :=
  if bit s i then i+1 else if 0 < i ∧ bit s (i-1) = true then i-1 else i

theorem sw_lt {n i : Nat} (s : Mask n) (h : i < n) : sw s i < n := by
  unfold sw
  split
  next ht => exact bit_true_lt s ht
  next => split <;> omega

theorem sw_invol {n i : Nat} (s : Mask n) : sw s (sw s i) = i := by
  by_cases h : bit s i = true
  · have hx := bits_disjoint s h
    simp [sw,h,hx]
  · have hf : bit s i = false := Bool.eq_false_iff.mpr h
    by_cases hp : 0 < i ∧ bit s (i-1)=true
    · have hg : sw s i=i-1 := by simp [sw,hf,hp]
      rw [hg]
      simp [sw,hp.2]
      omega
    · simp [sw,hf,hp]

def swPerm {n : Nat} (s : Mask n) : Perm n where
  toFun i := ⟨sw s i.val, sw_lt s i.isLt⟩
  invFun i := ⟨sw s i.val, sw_lt s i.isLt⟩
  left_inv i := Fin.ext (sw_invol s)
  right_inv i := Fin.ext (sw_invol s)

theorem sw_near {n i : Nat} (s : Mask n) : i-1 ≤ sw s i ∧ sw s i ≤ i+1 := by
  unfold sw
  split_ifs <;> omega

theorem sw_far {n i j : Nat} (s : Mask n) (_hj : j < n) (hij : i+2 ≤ j) :
    sw s i < sw s j := by
  have ha := (sw_near (i:=i) s).2
  have hb := (sw_near (i:=j) s).1
  by_cases hj : j=i+2
  · subst j
    by_cases ht : bit s i = true
    · have hx := bits_disjoint s ht
      simp [sw,ht,hx]
      split <;> omega
    · have hf : bit s i = false := Bool.eq_false_iff.mpr ht
      have hle : sw s i ≤ i := by
        simp [sw,hf]; split <;> omega
      omega
  · omega

theorem sw_desc {n i : Nat} (s : Mask n) (hi : i+1 < n) :
    sw s (i+1) < sw s i ↔ bit s i = true := by
  by_cases h0 : bit s i=true
  · have hf := bits_disjoint s h0
    simp [sw,h0,hf]
  · have hf : bit s i=false := Bool.eq_false_iff.mpr h0
    have hh : i+1 ≤ sw s (i+1) := by
      simp [sw,hf]
      (try split) <;> omega
    have hh' : sw s i ≤ i := by
      simp [sw,hf]
      (try split) <;> omega
    simp [hf]
    omega

theorem ext_inj_on {n : Nat} (f : Perm n) {a b : Nat} (ha : a<n) (hb : b<n) (h : ext f a=ext f b) :
    a=b := by
  simp only [ext, dif_pos ha,dif_pos hb] at h
  have hFin : (⟨a,ha⟩ : Fin n) = ⟨b,hb⟩ := f.injective (Fin.ext h)
  exact congrArg Fin.val hFin

def descMask {n : Nat} (f : Perm n) (hf : Far n f) : Mask n :=
  ⟨fun i => decide (i.val+1<n ∧ ext f (i.val+1) < ext f i.val),by
    constructor
    · intro i hi
      exact (of_decide_eq_true hi).1
    · intro i j e hi
      apply decide_eq_false
      intro hj
      have h0 := (of_decide_eq_true hi).2
      have h1 : ext f (j.val+1) < ext f j.val := hj.2
      have h2 := hf i.val (j.val+1) hj.1 (by omega)
      rw [←e] at h1 h2
      omega⟩

theorem desc_bit {n : Nat} (f : Perm n) (hf : Far n f) (i : Nat) (hi : i+1<n) :
    bit (descMask f hf) i = true ↔ ext f (i+1) < ext f i := by
  simp [bit,descMask,hi,show i<n by omega]

theorem swPerm_ext {n : Nat} (s : Mask n) (i : Nat) (hi : i<n) :
    ext (swPerm s) i = sw s i := by simp [ext,hi,swPerm]

theorem swPerm_far {n : Nat} (s : Mask n) : Far n (swPerm s) := by
  intro i j hj hij
  rw [swPerm_ext _ _ (by omega),swPerm_ext _ _ hj]
  exact sw_far s hj hij

theorem desc_sw_left {n : Nat} (s : Mask n) : descMask (swPerm s) (swPerm_far s) = s := by
  apply Subtype.ext
  funext i
  apply Bool.eq_iff_iff.mpr
  by_cases hi : i.val+1<n
  · rw [←bit_fin,desc_bit _ _ _ hi,swPerm_ext _ _ hi,swPerm_ext _ _ i.isLt,sw_desc _ hi,bit_fin]
  · have h := s.property.1 i
    simp [descMask,hi]
    exact Bool.eq_false_iff.mpr (fun h' => hi (h h'))

theorem sw_desc_right {n : Nat} (f : Perm n) (hf : Far n f) :
    swPerm (descMask f hf) = f := by
  let s := descMask f hf
  have hab : ∀ a b, a<b → b<n → (ext f a<ext f b ↔ sw s a<sw s b) := by
    intro a b h hb
    by_cases h' : a+2≤b
    · exact iff_of_true (hf a b hb h') (sw_far s hb h')
    · have e : b=a+1 := by omega
      subst b
      have hpa := (desc_bit f hf a hb).symm.trans (sw_desc s hb).symm
      have hp : ext f a ≠ ext f (a+1) := fun h' => by
        have hh := ext_inj_on f (by omega) hb h'
        omega
      have hs : sw s a ≠ sw s (a+1) := fun h' => by
        have hH := congrArg (sw s) h'
        rw [sw_invol,sw_invol] at hH
        omega
      omega
  have hall : ∀ a<n,∀ b<n, ext f a<ext f b ↔ sw s a<sw s b := by
    intro a ha b hb
    rcases Nat.lt_trichotomy a b with h|h|h
    · exact hab a b h hb
    · subst b
      simp
    · have hc := hab b a h ha
      have hp : ext f a ≠ ext f b := fun h' => by
        have hh := ext_inj_on f ha hb h'
        omega
      have hs : sw s a ≠ sw s b := fun h' => by
        have hh := congrArg (sw s) h'
        rw [sw_invol,sw_invol] at hh
        omega
      omega
  have hrank : ∀ i, i+1<n → ext f (sw s i)<ext f (sw s (i+1)) := by
    intro i hi
    apply (hall _ (sw_lt s (by omega : i<n)) _ (sw_lt s hi)).mpr
    rw [sw_invol,sw_invol]
    omega
  have hh := unique_ranks (fun i => ext f (sw s i)) n hrank (fun i hi => ext_lt f (sw_lt _ hi))
  apply perm_ext
  intro i hi
  rw [swPerm_ext _ _ hi]
  have he := hh (sw s i) (sw_lt s hi)
  change ext f (sw s (sw s i)) = sw s i at he
  rw [sw_invol] at he
  exact he.symm

/-- Countable model: permutations in the class are exactly monomer–dimer masks. -/
def avoidEquiv (n : Nat) (hn : 4 ≤ n) : {f : Perm n // avoids f forbidden4} ≃ Mask n where
  toFun f := descMask f.val (avoids_far n hn f.val f.property)
  invFun s := ⟨swPerm s,far_avoids n _ (swPerm_far s)⟩
  left_inv f := Subtype.ext (sw_desc_right f.val _)
  right_inv s := desc_sw_left s

end FibPopularity
