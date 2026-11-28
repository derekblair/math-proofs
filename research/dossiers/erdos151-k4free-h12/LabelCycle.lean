import ShortOdd
import LinkEncoded
import Mathlib.Logic.Equiv.Fintype

namespace BikovLocal

abbrev F7 := Fin 7

def cyclic (n i j : Nat) : Prop := i+1=j ∨ (i=0 ∧ j+1=n)

instance (n i j : Nat) : Decidable (cyclic n i j) := inferInstanceAs (Decidable (_ ∨ _))

def memc5 (i j : F7) : Prop := (i.val,j.val)∈c5
def memc7 (i j : F7) : Prop := (i.val,j.val)∈c7
def memextra (i j : F7) : Prop := (i.val,j.val)∈extra
instance (i j : F7) : Decidable (memc5 i j) := inferInstanceAs (Decidable (_∈c5))
instance (i j : F7) : Decidable (memc7 i j) := inferInstanceAs (Decidable (_∈c7))
instance (i j : F7) : Decidable (memextra i j) := inferInstanceAs (Decidable (_∈extra))

theorem c5_class : ∀ i j : F7, i<j → (memc5 i j ↔ j.val<5 ∧ cyclic 5 i.val j.val) := by decide +kernel
theorem c7_class : ∀ i j : F7, i<j → (memc7 i j ↔ cyclic 7 i.val j.val) := by decide +kernel
theorem extra_class : ∀ i j : F7, i<j → (memextra i j ↔ 5≤j.val) := by decide +kernel
theorem c5_mem_bound : ∀ e∈c5, e.1<e.2 ∧ e.2<7 := by decide +kernel

theorem classify_walk (R : F7→F7→Prop)
    (sym : ∀ ⦃a b⦄, R a b → R b a) (irr : ∀ a, ¬ R a a)
    (tri : ∀ a b c, R a b → R a c → R b c → False) :
    (∃ f : F7→Bool, ∀ ⦃x y⦄, R x y → f x≠f y) ∨
    (∃ k : Nat, (k=5 ∨ k=7) ∧ ∃ σ : Equiv.Perm F7,
      ∀ i j : F7, i<j → j.val<k → (R (σ i) (σ j) ↔ cyclic k i.val j.val)) := by
  classical
  by_cases h : ∃ x, ∃ p : Walk R x x,p.len%2=1
  · right
    obtain ⟨x,p,hp,distinct,chord⟩ := shortest_odd R sym h
    let toV (i : Fin p.len) := p.atV i.val
    have inj : Function.Injective toV := by
      intro a b h
      apply Fin.ext
      by_contra n
      rcases Nat.lt_or_gt_of_ne n with l|r
      · exact distinct _ _ l b.isLt h
      · exact distinct _ _ r a.isLt h.symm
    have bound : p.len≤7 := by simpa using Fintype.card_le_of_injective toV inj
    have not1 : p.len≠1 := by
      intro h
      have hh := p.step 0 (by omega)
      change R (p.atV 0) (p.atV 1) at hh
      rw [←h,p.first,p.last] at hh
      exact irr x hh
    have not3 : p.len≠3 := by
      intro h
      have h01 := p.step 0 (by omega)
      have h12 := p.step 1 (by omega)
      have h20 := p.step 2 (by omega)
      change R (p.atV 2) (p.atV 3) at h20
      have H : p.atV 3=p.atV 0 := by rw [←h,p.last,p.first]
      rw [H] at h20
      exact tri _ _ _ h01 (sym h20) h12
    have other : p.len=5 ∨ p.len=7 := by omega
    let emb (i : Fin p.len) : F7 := i.castLE bound
    have eInj : Function.Injective emb := fun _ _ h=>Fin.ext (congrArg (fun i : F7=>i.val) h)
    obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair emb toV eInj inj
    refine ⟨p.len,other,σ,?_⟩
    intro i j ij jn
    have in' : i.val<p.len := lt_trans ij jn
    have ei : σ i=p.atV i.val := hσ ⟨i.val,in'⟩
    have ej : σ j=p.atV j.val := hσ ⟨j.val,jn⟩
    rw [ei,ej]
    constructor
    · intro e
      by_contra! n
      have nn : i.val+1<j.val := by
        have hlt : i.val<j.val := ij
        have ne : i.val+1≠j.val := fun e=>n (Or.inl e)
        omega
      have nw : i.val≠0 ∨ j.val+1<p.len := by
        by_cases hi : i.val=0
        · exact Or.inr (by have nh : j.val+1≠p.len := fun e=>n (Or.inr ⟨hi,e⟩); omega)
        · exact Or.inl hi
      exact chord _ _ nn jn nw e
    · rintro (h|⟨h0,h1⟩)
      · rw [←h]
        exact p.step _ in'
      · have H : p.atV i.val=p.atV (j.val+1) := by rw [h0,h1,p.first,p.last]
        rw [H]
        exact sym (p.step _ jn)
  · exact Or.inl (bipartition_of_no_odd R sym h)

#print axioms classify_walk
end BikovLocal
