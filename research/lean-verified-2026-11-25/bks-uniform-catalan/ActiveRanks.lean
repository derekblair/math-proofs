import CorePosition

namespace FussCover
open Finset
variable {z h j : ℕ} (hj : 0<j) (hz : 0<z)
variable (r : Equiv.Perm (Fin (n z h j))) (P : packed r)

def raise (x : Fin (2*j)) : Fin (n z h j) :=
  ⟨hN z h j+1+x.val,by have e := n_eq_head_core (z:=z) (h:=h) hj; have := x.isLt; omega⟩

lemma raise_mono : StrictMono (raise (z:=z) (h:=h) hj) := by
  intro a b hab
  change a.val < b.val at hab
  change hN z h j+1+a.val < hN z h j+1+b.val
  omega

def lower (x : Fin (n z h j)) (lo : hN z h j < x.val)
    (hi : x.val < hN z h j+2*j+1) : Fin (2*j) :=
  ⟨x.val-(hN z h j+1),by omega⟩

lemma raise_lower (x : Fin (n z h j)) (lo : hN z h j < x.val)
    (hi : x.val < hN z h j+2*j+1) : raise hj (lower x lo hi)=x := by
  apply Fin.ext
  change hN z h j+1+(x.val-(hN z h j+1))=x.val
  omega

include hj hz P
lemma a_bounds (i : Fin j) :
    hN z h j < (r (A hj (aI i))).val ∧ (r (A hj (aI i))).val<hN z h j+2*j+1 := by
  have l := packed_A_anti hj r P (aI_lt i)
  have u := packed_A_before_Bmax hj r P (aI i)
  change (r (A hj (Fin.last j))).val < (r (A hj (aI i))).val at l
  change (r (A hj (aI i))).val < (r (B hj 0)).val at u
  rw [A_last_rank hj hz r P] at l
  rw [B_first_rank hj hz r P] at u
  exact ⟨l,u⟩

lemma b_bounds (i : Fin j) :
    hN z h j < (r (B hj (bI i))).val ∧ (r (B hj (bI i))).val<hN z h j+2*j+1 := by
  have l := packed_Amin_before_B hj r P (bI i)
  have u := packed_B_anti hj r P (bI_pos i)
  change (r (A hj (Fin.last j))).val < (r (B hj (bI i))).val at l
  change (r (B hj (bI i))).val < (r (B hj 0)).val at u
  rw [A_last_rank hj hz r P] at l
  rw [B_first_rank hj hz r P] at u
  exact ⟨l,u⟩

def U (i : Fin j) : Fin (2*j) :=
  lower (r (A hj (aI i))) (a_bounds hj hz r P i).1 (a_bounds hj hz r P i).2
def D (i : Fin j) : Fin (2*j) :=
  lower (r (B hj (bI i))) (b_bounds hj hz r P i).1 (b_bounds hj hz r P i).2

@[simp] lemma raise_U (i : Fin j) : raise hj (U hj hz r P i) = r (A hj (aI i)) :=
  raise_lower hj _ _ _
@[simp] lemma raise_D (i : Fin j) : raise hj (D hj hz r P i) = r (B hj (bI i)) :=
  raise_lower hj _ _ _

lemma U_mono : StrictMono (U hj hz r P) := by
  intro i l e
  apply (raise_mono (z:=z) (h:=h) hj).lt_iff_lt.mp
  rw [raise_U,raise_U]
  exact packed_A_anti hj r P (aI_anti e)
lemma D_mono : StrictMono (D hj hz r P) := by
  intro i l e
  apply (raise_mono (z:=z) (h:=h) hj).lt_iff_lt.mp
  rw [raise_D,raise_D]
  exact packed_B_anti hj r P (bI_anti e)

lemma crossing (i : Fin j) : U hj hz r P i < D hj hz r P i := by
  apply (raise_mono (z:=z) (h:=h) hj).lt_iff_lt.mp
  rw [raise_U,raise_D]
  exact local_cross hj r P i.rev

lemma disjoint_core (i l : Fin j) : U hj hz r P i ≠ D hj hz r P l := by
  intro e
  have f := congrArg (raise (z:=z) (h:=h) hj) e
  rw [raise_U,raise_D] at f
  have a := r.injective f
  let E := posEquiv (z:=z) (h:=h) hj hz
  have eq : E (.inr (.inl (aI i))) = E (.inr (.inr (bI l))) := a
  have eq' := E.injective eq
  cases eq'

lemma active_all (x : Fin (2*j)) :
    (∃ i, U hj hz r P i = x) ∨ (∃ i, D hj hz r P i = x) := by
  let E := posEquiv (z:=z) (h:=h) hj hz
  obtain ⟨v,hv⟩ := E.surjective (r.symm (raise hj x))
  have Y : r (E v)=raise hj x := by rw [hv,r.apply_symm_apply]
  cases v with
  | inl i =>
    have q : r (hAt hj hz i)=raise hj x := Y
    have iv := head_rank hj hz r P i
    rw [q] at iv
    change hN z h j+1+x.val=i.val at iv
    have := i.isLt
    omega
  | inr l =>
    cases l with
    | inl t =>
      have q : r (A hj t)=raise hj x := Y
      rcases allA t with el|⟨i,eq⟩
      · rw [el] at q
        have iv := A_last_rank hj hz r P
        rw [q] at iv
        change hN z h j+1+x.val=hN z h j at iv
        omega
      · rw [eq,←raise_U hj hz r P i] at q
        exact Or.inl ⟨i,(raise_mono (z:=z) (h:=h) hj).injective q⟩
    | inr t =>
      have q : r (B hj t)=raise hj x := Y
      rcases allB t with ez|⟨i,eq⟩
      · rw [ez] at q
        have iv := B_first_rank hj hz r P
        rw [q] at iv
        change hN z h j+1+x.val=hN z h j+2*j+1 at iv
        have := x.isLt
        omega
      · rw [eq,←raise_D hj hz r P i] at q
        exact Or.inr ⟨i,(raise_mono (z:=z) (h:=h) hj).injective q⟩

end FussCover
