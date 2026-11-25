import Topology

namespace ZFChain
open Finset
set_option maxHeartbeats 1500000

def Dominates {n} (D : Finset (V n)) : Prop :=
  ∀ x : V n, x ∈ D ∨ ∃ y ∈ D, adj x y

def pull {n} (D : Finset (V n)) (i : Fin (n+2)) : Finset (Fin 8) :=
  (D.filter fun v => blk v = i).image wire

theorem mem_pull {n} (D : Finset (V n)) (v : V n) :
    wire v ∈ pull D (blk v) ↔ v ∈ D := by
  constructor
  · intro h
    obtain ⟨w,hw,he⟩ := mem_image.mp h
    rcases mem_filter.mp hw with ⟨hm,hi⟩
    rwa [vertex_ext hi he] at hm
  · intro h
    exact mem_image.mpr ⟨v,mem_filter.mpr ⟨h,rfl⟩,rfl⟩

theorem card_pull {n} (D : Finset (V n)) (i : Fin (n+2)) :
    (pull D i).card = (D.filter fun v => blk v = i).card := by
  apply card_image_of_injOn
  intro v hv w hw he
  exact vertex_ext ((mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm) he

theorem localDomFrom {n} {D : Finset (V n)} {x y : V n}
    (hy : y ∈ D) (ha : adj x y) (hb : blk x = blk y) :
    localDominates (mid (blk x)) (pull D (blk x)) (wire x) := by
  right
  use wire y
  have hy' := (mem_pull D y).mpr hy
  rw [← hb] at hy'
  exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(adj_same hb).mp ha⟩,hy'⟩

theorem domCore_pull {n} {D : Finset (V n)} (hD : Dominates D) (i : Fin (n+2)) :
    domCore (mid i) (pull D i) := by
  intro a ha
  let v := lift i a (Or.inr (by omega))
  rcases hD v with h | ⟨y,hy,hy'⟩
  · exact Or.inl ((mem_pull D v).mpr h)
  · rcases hy' with hsame | hc
    · exact localDomFrom hy (Or.inl hsame) hsame.1
    · exact (core_not_cross (x := v) ha hc).elim

theorem chainDomLower {n} (D : Finset (V n)) (hD : Dominates D) :
    2*(n+2) + (n+2)/3 ≤ D.card := by
  let I := Fin (n+2)
  let H : Finset I := univ.filter (fun i => 2 < (pull D i).card)
  let midI : Finset I := univ.filter (fun i => 0 < i.val ∧ i.val < n+1)
  let prev : I → I := fun i => ⟨i.val - 1, by have := i.isLt; omega⟩
  let next : I → I := fun i => ⟨min (i.val+1) (n+1),by have := i.isLt; omega⟩
  have port_high {x : V n} (hx : x ∈ D) (hp : 6 ≤ (wire x).val) : blk x ∈ H := by
    have h2 := domCore_two _ (pull D (blk x)) (domCore_pull hD (blk x))
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    by_contra h
    have eq2 : (pull D (blk x)).card = 2 := by omega
    obtain ⟨h6,h7⟩ := domCore_port_cost _ _ (domCore_pull hD (blk x)) eq2
    have hh := (wire x).isLt
    have val := (mem_pull D x).mpr hx
    by_cases h' : (wire x).val = 6
    · have w : wire x = 6 := Fin.ext h'
      exact h6 (w ▸ val)
    · have w : wire x = 7 := Fin.ext (by omega)
      exact h7 (w ▸ val)
  have near : midI ⊆ H ∪ H.image prev ∪ H.image next := by
    intro i hi
    by_cases hH : i ∈ H
    · exact mem_union_left _ (mem_union_left _ hH)
    have hib := (mem_filter.mp hi).2
    have hm : mid i = true := by simp only [mid,decide_eq_true_eq]; omega
    have h2 := domCore_two _ (pull D i) (domCore_pull hD i)
    have eq2 : (pull D i).card = 2 := by
      have hu : ¬ (2 < (pull D i).card) := fun hu => hH (mem_filter.mpr ⟨mem_univ _,hu⟩)
      omega
    have hl : ∃ a : Fin 8, 6 ≤ a.val ∧ ¬ localDominates (mid i) (pull D i) a := by
      have hh := domCore_pull hD i
      rw [hm] at hh ⊢
      rcases domCore_middle_demand _ hh eq2 with hl | hr
      · exact ⟨6, by decide, hl⟩
      · exact ⟨7, by decide, hr⟩
    obtain ⟨a,ha,hbad⟩ := hl
    let x := lift i a (Or.inl hm)
    rcases hD x with hx | ⟨y,hy, he⟩
    · exact (hbad (Or.inl ((mem_pull D x).mpr hx))).elim
    · rcases he with he | he
      · exact (hbad (localDomFrom hy (Or.inl he) he.1)).elim
      · have hiy : 6 ≤ (wire y).val := by
          obtain ⟨e,(⟨_,rfl⟩|⟨_,rfl⟩)⟩ := he
          · simp
          · unfold left lift wire
            simp only [out]
            split <;> decide
        have hyn := port_high hy hiy
        obtain ⟨e,⟨hx,hy⟩|⟨hx,hy⟩⟩ := he
        · have hi' : i.val = e.val := congrArg (fun v => (blk v).val) hx
          rw [hy] at hyn
          have eh : prev (blk (right e)) = i := Fin.ext (by simp [prev,← hi'])
          exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨_,hyn,eh⟩))
        · have hi' : i.val = e.val+1 := congrArg (fun v => (blk v).val) hx
          rw [hy] at hyn
          have eh : next (blk (left e)) = i := Fin.ext (by
            have hlt := e.isLt
            simp [next,hi',Nat.min_eq_left (by omega : e.val+1 ≤ n+1)])
          exact mem_union_right _ (mem_image.mpr ⟨_,hyn,eh⟩)
  have mid_card : midI.card = n := by
    let midEmb : Fin n ↪ I := ⟨fun j => ⟨j.val+1,by have := j.isLt; omega⟩, fun a b h =>
      Fin.ext (Nat.succ.inj (congrArg Fin.val h))⟩
    have heq : (univ : Finset (Fin n)).map midEmb = midI := by
      ext i
      simp only [mem_map, mem_univ, true_and, midI, mem_filter]
      constructor
      · rintro ⟨x,rfl⟩
        have h := x.isLt
        change 0 < x.val+1 ∧ x.val+1 < n+1
        omega
      · intro h
        let x : Fin n := ⟨i.val-1,by omega⟩
        exact ⟨x,Fin.ext (by change i.val-1+1 = i.val; omega)⟩
    rw [← heq,card_map,card_univ,Fintype.card_fin]
  have cost : n ≤ 3 * H.card := calc
    n = midI.card := mid_card.symm
    _ ≤ (H ∪ H.image prev ∪ H.image next).card := card_le_card near
    _ ≤ H.card + (H.image prev).card + (H.image next).card :=
      (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    _ ≤ 3 * H.card := by
      have h₁ := card_image_le (s := H) (f := prev)
      have h₂ := card_image_le (s := H) (f := next)
      omega
  have addH (i : I) : 2 + (if i ∈ H then 1 else 0) ≤ (pull D i).card := by
    split
    · rename_i hi
      have hh := (mem_filter.mp hi).2
      omega
    · simpa using domCore_two _ (pull D i) (domCore_pull hD i)
  have hcost := sum_le_sum (s := (univ : Finset I)) (fun i _ => addH i)
  rw [sum_add_distrib, sum_const,card_univ,nsmul_eq_mul,Fintype.card_fin,
    sum_boole] at hcost
  have hHcard : (univ.filter fun i => i ∈ H).card = H.card := by simp
  rw [hHcard] at hcost
  simp_rw [card_pull] at hcost
  rw [sum_card_fiberwise_eq_card_filter] at hcost
  simp only [mem_univ, filter_true] at hcost
  change (n+2)*2 + H.card ≤ D.card at hcost
  change n ≤ 3 * H.card at cost
  omega

end ZFChain
