import HaarClass5DirTables
import HaarClass5L2Abelian

namespace HaarClass5TemplateClosure
open HaarClass5DirTables HaarReducedWalkCycle HaarClass3Collector64 HaarClass3Table
open HaarClass4Ports HaarClass4Generate HaarUniversal36 HaarHalfCollision
open scoped commutatorElement
variable {G H : Type*} [Group G] [Group H]

def eval (x y : G) (p : Coord) :=
  HaarClass3Collect.norm x y (portC x y) (portU x y) (portV x y) p

theorem central_2 (nil : L G 3 = ⊥) {a : G} (ha : a ∈ L G 2) (b : G) : Commute a b := by
  apply commutatorElement_eq_one_iff_commute.mp
  have h := next ha b
  change ⁅a,b⁆ ∈ L G 3 at h
  rw [nil] at h
  exact Subgroup.mem_bot.mp h

theorem path_matches (nil : L G 3=⊥) (x y : G) (w : List (Fin 3))
    (T : ℕ → Coord) (N : ℕ) (h0 : T 0=(0,0,0,0,0))
    (hS : ∀ i<N, (label w i=2 → Range (T i).1) ∧
      T (i+1)=move (decide (i%2=0)) (label w i) (T i)) (i : ℕ) (hi : i ≤ N) :
    path x y w i = eval x y (T i) := by
  have uc := central_2 nil (layer_u x y)
  have vc := central_2 nil (layer_v x y)
  have rx := HaarClass4Data.right_of_left (show ⁅portC x y,x⁆=portU x y from rfl) uc
  have ry := HaarClass4Data.right_of_left (show ⁅portC x y,y⁆=portV x y from rfl) vc
  induction i with
  | zero => simp [path,h0,eval,HaarClass3Collect.norm]
  | succ i ih =>
    obtain ⟨hR,hT⟩ := hS i (by omega)
    rw [path,ih (by omega),hT]
    have E := norm_move x y (portC x y) (portU x y) (portV x y) uc vc (ports_xy x y) rx ry
      (decide (i%2=0)) (label w i) (T i) hR
    simpa [eval,signPort] using E.symm

theorem path_full (x y : G) (w : List (Fin 3)) : path x y w w.length = prodFrom x y 0 w := by
  have p := segment_product x y (path x y w) (label w) 0 0 w.length
    (by intro; intros; simp only [Nat.zero_add,path])
  simpa [path,segment_label] using p

theorem map_sign (f : G →* H) (x y : G) (i : ℕ) (c : Fin 3) :
    f (signPort x y i c)=signPort (f x) (f y) i c := by
  fin_cases c <;> by_cases h : i%2=0 <;> simp [signPort,port,h]

theorem map_prod (f : G →* H) (x y : G) (i : ℕ) (w : List (Fin 3)) :
    f (prodFrom x y i w)=prodFrom (f x) (f y) i w := by
  induction w generalizing i with
  | nil => simp [prodFrom]
  | cons c t ih => simp [prodFrom,ih,map_sign]

theorem map_path (f : G →* H) (x y : G) (w : List (Fin 3)) (i : ℕ) :
    f (path x y w i)=path (f x) (f y) w i := by
  induction i with
  | zero => simp [path]
  | succ i ih => simp [path,ih,map_sign]

theorem quote_nil (n : ℕ) : L (G ⧸ L G n) n=⊥ := by
  let S := L G n
  let f := QuotientGroup.mk' S
  change L (G ⧸ S) n = ⊥
  have e : (L G n).map f = L (G ⧸ S) n := map_ls f (QuotientGroup.mk'_surjective S) n
  rw [← e,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']

theorem tail_word (x y : G) (w : List (Fin 3)) (T : ℕ → Coord)
    (h0 : T 0=(0,0,0,0,0))
    (hS : ∀ i<w.length, (label w i=2 → Range (T i).1) ∧
      T (i+1)=move (decide (i%2=0)) (label w i) (T i))
    (hg : (T w.length).1=0 ∧ (T w.length).2.1=0 ∧ (T w.length).2.2.1=0) :
    prodFrom x y 0 w ∈ L G 2 := by
  let S := L G 2
  let f := QuotientGroup.mk' S
  have n2 : L (G ⧸ S) 2=⊥ := quote_nil 2
  have n3 : L (G ⧸ S) 3=⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup (G ⧸ S)) (by decide : 2 ≤ 3)).trans (le_of_eq n2)
  have hu : portU (f x) (f y)=1 := by
    have h := layer_u (f x) (f y)
    change portU (f x) (f y) ∈ L (G ⧸ S) 2 at h
    rw [n2] at h
    exact Subgroup.mem_bot.mp h
  have hv : portV (f x) (f y)=1 := by
    have h := layer_v (f x) (f y)
    change portV (f x) (f y) ∈ L (G ⧸ S) 2 at h
    rw [n2] at h
    exact Subgroup.mem_bot.mp h
  apply (QuotientGroup.eq_one_iff (N:=S) _).mp
  change f (prodFrom x y 0 w)=1
  rw [map_prod,← path_full,path_matches n3 _ _ _ T w.length h0 hS _ le_rfl]
  simp [eval,HaarClass3Collect.norm,hg.1,hg.2.1,hg.2.2,hu,hv]

theorem A_tail (x y : G) (t : Fin 4) : prodFrom x y 0 (A t) ∈ L G 2 := by
  apply tail_word x y (A t) (rowsA t) (A_zero t)
  · intro i h
    rw [A_len] at h
    exact A_steps t ⟨i,h⟩
  · rw [A_len]; exact A_grade t

theorem B_tail (x y : G) (t : Fin 4) : prodFrom x y 0 (B t) ∈ L G 2 := by
  apply tail_word x y (B t) (rowsB t) (B_zero t)
  · intro i h
    rw [B_len] at h
    exact B_steps t ⟨i,h⟩
  · rw [B_len]; exact B_grade t

theorem prod_append (x y : G) (i : ℕ) (A B : List (Fin 3)) :
    prodFrom x y i (A++B)=prodFrom x y i A * prodFrom x y (i+A.length) B := by
  induction A generalizing i with
  | nil => simp [prodFrom]
  | cons c A ih =>
    simp only [List.cons_append,prodFrom,List.length_cons,ih,mul_assoc]
    rw [show i+1+A.length=i+(A.length+1) by omega]

theorem prod_same_sign (x y : G) (i j : ℕ) (w : List (Fin 3))
    (h : i%2=j%2) : prodFrom x y i w=prodFrom x y j w := by
  induction w generalizing i j with
  | nil => rfl
  | cons c w ih => rw [prodFrom,prodFrom,ih (i+1) (j+1) (by omega)]; simp [signPort,h]

theorem inv_sign (x y : G) (i j : ℕ) (c : Fin 3) (opp : (i+j)%2=1) :
    signPort x y i c=(signPort x y j c)⁻¹ := by
  by_cases h : i%2=0
  · have hd : j%2≠0 := by omega
    simp [signPort,h,hd]
  · have hd : j%2=0 := by omega
    simp [signPort,h,hd]

theorem prod_reverse (x y : G) (i j : ℕ) (w : List (Fin 3))
    (h : (i+j+w.length)%2=0) : prodFrom x y i w.reverse=(prodFrom x y j w)⁻¹ := by
  induction w generalizing i j with
  | nil => simp [prodFrom]
  | cons c w ih =>
    rw [List.reverse_cons,prod_append,List.length_reverse, ih i (j+1) (by simp at h; omega)]
    simp only [prodFrom,mul_one,mul_inv_rev]
    rw [inv_sign x y (i+w.length) j c (by simp at h; omega)]

theorem all_closed (nil : L G 5=⊥) (x y : G) (t : Fin 4) : prodFrom x y 0 (W t)=1 := by
  rw [concat]
  simp only [prod_append,List.length_append,A_len,B_len,List.length_reverse]
  have pB : prodFrom x y (0+12) (B t) = prodFrom x y 0 (B t) :=
    prod_same_sign x y _ _ _ (by decide)
  rw [pB,prod_reverse x y (0+12+20) 0 (A t) (by rw [A_len]),
    prod_reverse x y (0+12+20+12) 0 (B t) (by rw [B_len])]
  exact (HaarClass5L2Abelian.l2_comm nil (A_tail x y t) (B_tail x y t)).commutator_eq

end HaarClass5TemplateClosure
#print axioms HaarClass5TemplateClosure.all_closed
