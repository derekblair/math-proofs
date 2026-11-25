import ChainLocal
import Interface
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace ZFChain
open Finset

def mid {n : ℕ} (i : Fin (n+2)) : Bool := decide (0 < i.val ∧ i.val + 1 < n+2)
def out {n : ℕ} (i : Fin (n+2)) : Fin 8 := if mid i then 7 else 6
def V (n : ℕ) := {p : Fin (n+2) × Fin 8 // legal (mid p.1) p.2}
instance (n) : Fintype (V n) := by unfold V; infer_instance
instance (n) : DecidableEq (V n) := by unfold V; infer_instance
def blk {n} (v : V n) : Fin (n+2) := v.val.1
def wire {n} (v : V n) : Fin 8 := v.val.2
def lift {n} (i : Fin (n+2)) (a : Fin 8) (h : legal (mid i) a) : V n := ⟨(i,a),h⟩
@[simp] theorem blk_lift {n} (i : Fin (n+2)) (a) (h) : blk (lift i a h) = i := rfl
@[simp] theorem wire_lift {n} (i : Fin (n+2)) (a) (h) : wire (lift i a h) = a := rfl
theorem lift_eta {n} (v : V n) : lift (blk v) (wire v) v.property = v := by cases v; rfl
theorem vertex_ext {n} {a b : V n} (h₁ : blk a = blk b) (h₂ : wire a = wire b) : a = b :=
  Subtype.ext (Prod.ext h₁ h₂)
def left {n} (e : Fin (n+1)) : V n :=
  lift e.castSucc (out e.castSucc) (by unfold out; split <;> simp_all [legal])
def right {n} (e : Fin (n+1)) : V n := lift e.succ 6 (Or.inr (by decide))

def Cross {n} (x y : V n) : Prop :=
  ∃ e, (x = left e ∧ y = right e) ∨ (x = right e ∧ y = left e)
def adj {n} (x y : V n) : Prop :=
  (blk x = blk y ∧ localEdge (mid (blk x)) (wire x) (wire y) = true) ∨ Cross x y

theorem cross_ne {n} {x y : V n} (h : Cross x y) : blk x ≠ blk y := by
  obtain ⟨e,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩ := h
  all_goals
    intro he
    have hm := congrArg Fin.val he
    change _ at hm
    simp [blk,left,right,lift] at hm

theorem adj_symm {n} {x y : V n} (h : adj x y) : adj y x := by
  rcases h with ⟨h,q⟩ | ⟨e,⟨h,q⟩ | ⟨h,q⟩⟩
  · exact Or.inl ⟨h.symm,by rw [← h,localEdge_symm]; exact q⟩
  · exact Or.inr ⟨e,Or.inr ⟨q,h⟩⟩
  · exact Or.inr ⟨e,Or.inl ⟨q,h⟩⟩
theorem adj_irrefl {n} (x : V n) : ¬ adj x x := by
  rintro (⟨_,h⟩ | h)
  · rw [localEdge_diag] at h
    contradiction
  · exact cross_ne h rfl

def chain (n : ℕ) : SimpleGraph (V n) where
  Adj := adj
  symm := ⟨fun _ _ => adj_symm⟩
  loopless := ⟨adj_irrefl⟩

theorem adj_same {n} {x y : V n} (h : blk x = blk y) :
    adj x y ↔ localEdge (mid (blk x)) (wire x) (wire y) = true := by
  constructor
  · rintro (⟨_,q⟩|q)
    · exact q
    · exact (cross_ne q h).elim
  · exact fun q => Or.inl ⟨h,q⟩

theorem fort_has_two {m : Bool} {F : Finset (Fin 8)}
    (h : locFort m F) {a u : Fin 8} (ha : a ∉ F) (hu : u ∈ F)
    (he : localEdge m a u = true) :
    ∃ v ∈ F, localEdge m a v = true ∧ v ≠ u := by
  have hu' : u ∈ locNbr m a ∩ F := by simp [locNbr, hu, he]
  by_contra! H
  have hsub : locNbr m a ∩ F ⊆ {u} := by
    intro x hx
    have hg : x ∈ F ∧ localEdge m a x = true := by
      simpa [mem_inter, locNbr, and_comm] using hx
    simpa using H x hg.1 hg.2
  have hEq : locNbr m a ∩ F = {u} := Subset.antisymm hsub (singleton_subset_iff.mpr hu')
  exact h.2.2 _ ha (by simp [hEq])

theorem liftFort {n} {i : Fin (n+2)} {F : Finset (Fin 8)} (h : locFort (mid i) F) :
    BlockFort adj blk i (F.attach.image (fun a : F => lift i a.val (h.2.1 _ a.property))) := by
  let G := F.attach.image (fun a : F => lift i a.val (h.2.1 _ a.property))
  have hh (v : V n) : v ∈ G ↔ blk v = i ∧ wire v ∈ F := by
    constructor
    · intro hv
      obtain ⟨a,_,rfl⟩ := mem_image.mp hv
      exact ⟨rfl,a.property⟩
    · rintro ⟨hb,hw⟩
      exact mem_image.mpr ⟨⟨wire v,hw⟩,mem_attach _ _,vertex_ext hb.symm rfl⟩
  change BlockFort adj blk i G
  refine ⟨?_,fun v hv => (hh v |>.mp hv).1,?_⟩
  · obtain ⟨a,ha⟩ := h.1
    exact ⟨lift i a (h.2.1 _ ha), (hh _).mpr ⟨rfl,ha⟩⟩
  · intro x hx hxF y hy he
    have hy' := (hh y).mp hy
    have fx : wire x ∉ F := fun hf => hxF ((hh _).mpr ⟨hx,hf⟩)
    have ex := (adj_same (hx.trans hy'.1.symm)).mp he
    rw [hx] at ex
    obtain ⟨a,ha,hab,hne⟩ := fort_has_two h fx hy'.2 ex
    let z := lift i a (h.2.1 _ ha)
    have hz : blk z = i := rfl
    have hw : wire z = a := rfl
    refine ⟨z,(hh _).mpr ⟨hz,hw.symm ▸ ha⟩,?_,?_⟩
    · apply (adj_same (hx.trans hz.symm)).mpr
      simpa [hx,hw] using hab
    · intro heq
      exact hne (hw.symm.trans (congrArg wire heq))

theorem chainLocalSmall (n : ℕ) (i : Fin (n+2)) (S : Finset (V n))
    (hs : (S.filter (fun y => blk y = i)).card < 4) :
    ∃ F, BlockFort adj blk i F ∧ Disjoint F S := by
  classical
  let T := (S.filter (fun y => blk y = i)).image wire
  have ht : T.card < 4 := (card_image_le (f := wire)).trans_lt hs
  obtain ⟨F,hmem,hdis⟩ := local_Forts_hit (mid i) T ht
  have hf := local_Forts_correct (mid i) F hmem
  refine ⟨_,liftFort hf,?_⟩
  rw [disjoint_left] at hdis ⊢
  intro v hv hvS
  obtain ⟨a,_,rfl⟩ := mem_image.mp hv
  exact hdis a.property (mem_image.mpr ⟨_,mem_filter.mpr ⟨hvS,rfl⟩,rfl⟩)

theorem chainForcingLower (n : ℕ) (S : Finset (V n)) (hs : Reach adj S univ) :
    3 * (n+2) + 1 ≤ S.card := by
  have h := forceLower adj (@blk n) (@left n) (@right n) 4
      (fun x y hx hne => hx.resolve_left (fun hh => hne hh.1))
      (chainLocalSmall n) S hs
  simp only [Fintype.card_fin] at h
  omega

end ZFChain
