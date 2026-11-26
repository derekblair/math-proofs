import HaarClass6Commute
import HaarP3Class4Collect
import HaarP3LayerGenBridge
import HaarClass5TemplateCycles
import HaarAnyPorts

namespace HaarClass7Parallel
open HaarUniversal36 HaarClass6Commute HaarClass4Table HaarClass4Normal
open HaarP3Class4Collect HaarClass4Ports HaarClass4Generate HaarP3LayerGen
open HaarReducedWalkCycle HaarHalfCollision HaarAllNoncommuting
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem prefix_eval (nil : L G 4=⊥) (x y : G) (w : List (Fin 3)) (r : ℕ → Row)
    (z : r 0=base)
    (s : ∀ i < w.length, (label w i=2 → range4 (r i).i) ∧
      r (i+1)=move (decide (i%2=0)) (label w i) (r i))
    (i : ℕ) (hi : i≤w.length) :
    path x y w i = eval (make nil x y) (r i) := by
  induction i with
  | zero => rw [z]; simp [path,eval,base,mid,HaarClass4Normal.tail]
  | succ i ih =>
    obtain ⟨rng,eq⟩ := s i (by omega)
    rw [path,ih (by omega),eq]
    simpa [make,signPort] using
      (step_eval (make nil x y) (decide (i%2=0)) (label w i) (r i) rng).symm

theorem in_gamma3 (x y : G) (w : List (Fin 3)) (r : ℕ → Row)
    (z : r 0=base)
    (s : ∀ i < w.length, (label w i=2 → range4 (r i).i) ∧
      r (i+1)=move (decide (i%2=0)) (label w i) (r i))
    (endp : (r w.length).i=0 ∧ (r w.length).j=0 ∧ (r w.length).c=0) :
    prodFrom x y 0 w ∈ L G 2 := by
  let f := QuotientGroup.mk' (L G 4)
  let H := G ⧸ L G 4
  let M := make (ls4quot_class4 G) (f x) (f y)
  have eq := prefix_eval (ls4quot_class4 G) (f x) (f y) w r z s w.length (by omega)
  rw [HaarClass5TemplateClosure.path_full] at eq
  rw [← HaarClass5TemplateClosure.map_prod] at eq
  rcases endp with ⟨hi,hj,hc⟩
  have eu : M.u∈L H 2 := layer_u (f x) (f y)
  have ev : M.v∈L H 2 := layer_v (f x) (f y)
  have le32 : L H 3 ≤ L H 2 := Subgroup.lowerCentralSeries_antitone _ (by decide : 2≤3)
  obtain ⟨ha,hb,hd⟩ := tail_layers (ls4quot_class4 G) (f x) (f y)
  have e : f (prodFrom x y 0 w) ∈ L H 2 := by
    rw [eq]
    change eval M (r w.length) ∈ L H 2
    simp only [eval,hi,hj,hc,zpow_zero,one_mul,mid,HaarClass4Normal.tail]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.zpow_mem _ eu _) (Subgroup.zpow_mem _ ev _))
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.zpow_mem _ (le32 ha) _)
        (Subgroup.zpow_mem _ (le32 hb) _)) (Subgroup.zpow_mem _ (le32 hd) _))
  have m : (L G 2).map f = L H 2 := map_ls f (QuotientGroup.mk'_surjective (L G 4)) 2
  rw [←m] at e
  obtain ⟨q,hq,h⟩ := e
  have d : q⁻¹ * prodFrom x y 0 w ∈ L G 4 := (QuotientGroup.eq_one_iff _).mp (by
    change f (q⁻¹ * prodFrom x y 0 w)=1
    rw [map_mul,map_inv,h,inv_mul_cancel])
  have le42 : L G 4 ≤ L G 2 := Subgroup.lowerCentralSeries_antitone _ (by decide : 2≤4)
  simpa [←mul_assoc] using (Subgroup.mul_mem (L G 2) hq (le42 d))

theorem commute_words (nil : L G 7=⊥) (x y : G) (a b : List (Fin 3))
    (ha : prodFrom x y 0 a ∈ L G 2)
    (he : let f := QuotientGroup.mk' (L G 4);
      prodFrom (f x) (f y) 0 a = prodFrom (f x) (f y) 0 b) :
    Commute (prodFrom x y 0 a) (prodFrom x y 0 b) := by
  let A := prodFrom x y 0 a
  let B := prodFrom x y 0 b
  let f := QuotientGroup.mk' (L G 4)
  let z := B*A⁻¹
  have h : f A=f B := by
    change f (prodFrom x y 0 a)=f (prodFrom x y 0 b)
    rw [HaarClass5TemplateClosure.map_prod,HaarClass5TemplateClosure.map_prod]
    exact he
  have hz : z∈L G 4 := (QuotientGroup.eq_one_iff _).mp (by
    change f (B*A⁻¹)=1
    rw [map_mul,map_inv,h,mul_inv_cancel])
  have e : B = z*A := by dsimp [z]; group
  change Commute A B
  rw [e]
  exact (central_L2 4 nil hz ha).symm.mul_right (Commute.refl _)

def A0 : List (Fin 3) := [0,1,0,1,2,0,1,2,0,2,1,0,2,0]
def dataA0 : Array Row := #[⟨0,0,0,0,0,0,0,0⟩,⟨0,0,0,0,0,0,0,0⟩,⟨-1,0,0,0,0,0,0,0⟩,⟨-1,0,0,0,0,0,0,0⟩,⟨-2,0,0,0,0,0,0,0⟩,⟨-2,1,-2,3,0,-1,0,0⟩,⟨-2,1,-2,3,0,-1,0,0⟩,⟨-1,1,-2,1,0,0,0,0⟩,⟨-1,0,-1,0,1,0,0,0⟩,⟨-1,0,-1,0,1,0,0,0⟩,⟨-1,-1,0,-1,1,0,1,-1⟩,⟨0,-1,0,-1,1,-1,2,-1⟩,⟨0,-1,0,-1,1,-1,2,-1⟩,⟨0,0,0,-1,1,-1,1,0⟩,⟨0,0,0,-1,1,-1,1,0⟩]
def rowA0 (i : ℕ) : Row := dataA0[i]!
theorem stepsA0 (i : ℕ) (hi : i<A0.length) :
    (label A0 i=2 → range4 (rowA0 i).i) ∧
    rowA0 (i+1)=move (decide (i%2=0)) (label A0 i) (rowA0 i) := by
  have ht : ∀ i : Fin 14, (label A0 i.val=2 → range4 (rowA0 i.val).i) ∧
      rowA0 (i.val+1)=move (decide (i.val%2=0)) (label A0 i.val) (rowA0 i.val) := by decide
  exact ht ⟨i,hi⟩

def B0 : List (Fin 3) := [0,1,0,2,1,0,2,1,0,1,2,0,1,2,1,0]
def dataB0 : Array Row := #[⟨0,0,0,0,0,0,0,0⟩,⟨0,0,0,0,0,0,0,0⟩,⟨-1,0,0,0,0,0,0,0⟩,⟨-1,0,0,0,0,0,0,0⟩,⟨-1,-1,1,-1,-1,0,1,0⟩,⟨0,-1,1,0,-1,0,0,0⟩,⟨0,-1,1,0,-1,0,0,0⟩,⟨0,0,1,0,0,0,0,0⟩,⟨-1,0,1,-1,0,0,0,0⟩,⟨-1,0,1,-1,0,0,0,0⟩,⟨-2,0,1,-2,0,1,0,0⟩,⟨-2,1,-1,1,1,0,-2,1⟩,⟨-2,1,-1,1,1,0,-2,1⟩,⟨-1,1,-1,0,1,0,-1,1⟩,⟨-1,0,0,-1,1,0,0,0⟩,⟨0,0,0,-1,1,-1,1,0⟩,⟨0,0,0,-1,1,-1,1,0⟩]
def rowB0 (i : ℕ) : Row := dataB0[i]!
theorem stepsB0 (i : ℕ) (hi : i<B0.length) :
    (label B0 i=2 → range4 (rowB0 i).i) ∧
    rowB0 (i+1)=move (decide (i%2=0)) (label B0 i) (rowB0 i) := by
  have ht : ∀ i : Fin 16, (label B0 i.val=2 → range4 (rowB0 i.val).i) ∧
      rowB0 (i.val+1)=move (decide (i.val%2=0)) (label B0 i.val) (rowB0 i.val) := by decide
  exact ht ⟨i,hi⟩

def W0 : List (Fin 3) := [1,2,0,1,2,0,2,1,0,2,1,0,2,1,0,2,1,0,1,2,0,1,2,1,2,0,1,2,0,2,1,0,2,1,0,2,1,0,2,1,0,1,2,0,1,2]

set_option maxHeartbeats 2000000 in
theorem form0 (x y : G) :
    prodFrom x y 0 W0 = (x⁻¹) * ⁅prodFrom x⁻¹ y⁻¹ 0 A0,prodFrom x⁻¹ y⁻¹ 0 B0⁆ * (x⁻¹)⁻¹ := by
  norm_num [W0,A0,B0,prodFrom,signPort,port,commutatorElement_def] <;> group

theorem close0 (nil : L G 7=⊥) (x y : G) : prodFrom x y 0 W0=1 := by
  have ord (X Y : G) : prodFrom X Y 0 A0 ∈ L G 2 :=
    in_gamma3 X Y A0 rowA0 (by decide) stepsA0 (by decide)
  have proj (X Y : G ⧸ L G 4) :
      prodFrom X Y 0 A0 = prodFrom X Y 0 B0 := by
    have a := prefix_eval (ls4quot_class4 G) X Y A0 rowA0 (by decide) stepsA0 A0.length (by omega)
    have b := prefix_eval (ls4quot_class4 G) X Y B0 rowB0 (by decide) stepsB0 B0.length (by omega)
    rw [HaarClass5TemplateClosure.path_full] at a b
    have e : rowA0 A0.length = rowB0 B0.length := by decide
    rw [e] at a
    exact a.trans b.symm
  rw [form0,(commute_words nil x⁻¹ y⁻¹ A0 B0 (ord x⁻¹ y⁻¹)
    (proj _ _)).commutator_eq]
  group

def A1 : List (Fin 3) := [0,1,0,1,2,0,1,0,2,1,0,2,1,2,1,0]
def dataA1 : Array Row := #[⟨0,0,0,0,0,0,0,0⟩,⟨0,0,0,0,0,0,0,0⟩,⟨-1,0,0,0,0,0,0,0⟩,⟨-1,0,0,0,0,0,0,0⟩,⟨-2,0,0,0,0,0,0,0⟩,⟨-2,1,-2,3,0,-1,0,0⟩,⟨-2,1,-2,3,0,-1,0,0⟩,⟨-1,1,-2,1,0,0,0,0⟩,⟨-1,1,-2,1,0,0,0,0⟩,⟨-1,2,-3,2,-2,0,1,-2⟩,⟨-2,2,-3,5,-2,-2,3,-2⟩,⟨-2,2,-3,5,-2,-2,3,-2⟩,⟨-2,1,-1,2,-1,-1,1,0⟩,⟨-1,1,-1,1,-1,0,0,0⟩,⟨-1,0,0,0,-1,0,0,1⟩,⟨0,0,0,0,-1,0,-1,1⟩,⟨0,0,0,0,-1,0,-1,1⟩]
def rowA1 (i : ℕ) : Row := dataA1[i]!
theorem stepsA1 (i : ℕ) (hi : i<A1.length) :
    (label A1 i=2 → range4 (rowA1 i).i) ∧
    rowA1 (i+1)=move (decide (i%2=0)) (label A1 i) (rowA1 i) := by
  have ht : ∀ i : Fin 16, (label A1 i.val=2 → range4 (rowA1 i.val).i) ∧
      rowA1 (i.val+1)=move (decide (i.val%2=0)) (label A1 i.val) (rowA1 i.val) := by decide
  exact ht ⟨i,hi⟩

def B1 : List (Fin 3) := [2,1,2,1,0,2,1,2,0,1,2,0,1,0,1,2]
def dataB1 : Array Row := #[⟨0,0,0,0,0,0,0,0⟩,⟨0,1,0,0,0,0,0,0⟩,⟨-1,1,0,0,0,0,0,0⟩,⟨-1,2,-1,1,0,0,0,0⟩,⟨-2,2,-1,2,0,-1,0,0⟩,⟨-2,2,-1,2,0,-1,0,0⟩,⟨-2,1,1,-1,-1,0,1,0⟩,⟨-1,1,1,0,-1,0,0,0⟩,⟨-1,0,2,-1,-3,0,1,1⟩,⟨-1,0,2,-1,-3,0,1,1⟩,⟨-2,0,2,-3,-3,1,4,1⟩,⟨-2,1,0,0,-1,0,1,0⟩,⟨-2,1,0,0,-1,0,1,0⟩,⟨-1,1,0,0,-1,0,0,0⟩,⟨-1,1,0,0,-1,0,0,0⟩,⟨0,1,0,0,-1,0,-1,0⟩,⟨0,0,0,0,-1,0,-1,1⟩]
def rowB1 (i : ℕ) : Row := dataB1[i]!
theorem stepsB1 (i : ℕ) (hi : i<B1.length) :
    (label B1 i=2 → range4 (rowB1 i).i) ∧
    rowB1 (i+1)=move (decide (i%2=0)) (label B1 i) (rowB1 i) := by
  have ht : ∀ i : Fin 16, (label B1 i.val=2 → range4 (rowB1 i.val).i) ∧
      rowB1 (i.val+1)=move (decide (i.val%2=0)) (label B1 i.val) (rowB1 i.val) := by decide
  exact ht ⟨i,hi⟩

def W1 : List (Fin 3) := [0,1,0,1,2,0,1,0,2,1,0,2,1,2,1,0,2,1,2,1,0,2,1,2,0,1,2,0,1,0,1,2,0,1,2,1,2,0,1,2,0,1,0,2,1,0,1,0,2,1,0,1,0,2,1,0,2,1,2,0,1,2,1,2]

set_option maxHeartbeats 2000000 in
theorem form1 (x y : G) :
    prodFrom x y 0 W1 = (1) * ⁅prodFrom x y 0 A1,prodFrom x y 0 B1⁆ * (1)⁻¹ := by
  norm_num [W1,A1,B1,prodFrom,signPort,port,commutatorElement_def] <;> group

theorem close1 (nil : L G 7=⊥) (x y : G) : prodFrom x y 0 W1=1 := by
  have ord (X Y : G) : prodFrom X Y 0 A1 ∈ L G 2 :=
    in_gamma3 X Y A1 rowA1 (by decide) stepsA1 (by decide)
  have proj (X Y : G ⧸ L G 4) :
      prodFrom X Y 0 A1 = prodFrom X Y 0 B1 := by
    have a := prefix_eval (ls4quot_class4 G) X Y A1 rowA1 (by decide) stepsA1 A1.length (by omega)
    have b := prefix_eval (ls4quot_class4 G) X Y B1 rowB1 (by decide) stepsB1 B1.length (by omega)
    rw [HaarClass5TemplateClosure.path_full] at a b
    have e : rowA1 A1.length = rowB1 B1.length := by decide
    rw [e] at a
    exact a.trans b.symm
  rw [form1,(commute_words nil x y A1 B1 (ord x y)
    (proj _ _)).commutator_eq]
  group

def A2 : List (Fin 3) := [0,1,0,1,2,0,1,2,0,2,1,0,2,0]
def dataA2 : Array Row := #[⟨0,0,0,0,0,0,0,0⟩,⟨0,0,0,0,0,0,0,0⟩,⟨-1,0,0,0,0,0,0,0⟩,⟨-1,0,0,0,0,0,0,0⟩,⟨-2,0,0,0,0,0,0,0⟩,⟨-2,1,-2,3,0,-1,0,0⟩,⟨-2,1,-2,3,0,-1,0,0⟩,⟨-1,1,-2,1,0,0,0,0⟩,⟨-1,0,-1,0,1,0,0,0⟩,⟨-1,0,-1,0,1,0,0,0⟩,⟨-1,-1,0,-1,1,0,1,-1⟩,⟨0,-1,0,-1,1,-1,2,-1⟩,⟨0,-1,0,-1,1,-1,2,-1⟩,⟨0,0,0,-1,1,-1,1,0⟩,⟨0,0,0,-1,1,-1,1,0⟩]
def rowA2 (i : ℕ) : Row := dataA2[i]!
theorem stepsA2 (i : ℕ) (hi : i<A2.length) :
    (label A2 i=2 → range4 (rowA2 i).i) ∧
    rowA2 (i+1)=move (decide (i%2=0)) (label A2 i) (rowA2 i) := by
  have ht : ∀ i : Fin 14, (label A2 i.val=2 → range4 (rowA2 i.val).i) ∧
      rowA2 (i.val+1)=move (decide (i.val%2=0)) (label A2 i.val) (rowA2 i.val) := by decide
  exact ht ⟨i,hi⟩

def B2 : List (Fin 3) := [2,1,0,2,0,2,1,0,2,1,0,1,2,0,1,0,1,2]
def dataB2 : Array Row := #[⟨0,0,0,0,0,0,0,0⟩,⟨0,1,0,0,0,0,0,0⟩,⟨-1,1,0,0,0,0,0,0⟩,⟨-1,1,0,0,0,0,0,0⟩,⟨-1,0,1,-1,-1,0,1,0⟩,⟨-1,0,1,-1,-1,0,1,0⟩,⟨-1,-1,2,-2,-3,0,3,1⟩,⟨0,-1,2,0,-3,0,0,1⟩,⟨0,-1,2,0,-3,0,0,1⟩,⟨0,0,2,0,-1,0,0,0⟩,⟨-1,0,2,-2,-1,0,1,0⟩,⟨-1,0,2,-2,-1,0,1,0⟩,⟨-2,0,2,-4,-1,2,2,0⟩,⟨-2,1,0,-1,1,1,-2,1⟩,⟨-2,1,0,-1,1,1,-2,1⟩,⟨-1,1,0,-1,1,0,-1,1⟩,⟨-1,1,0,-1,1,0,-1,1⟩,⟨0,1,0,-1,1,-1,0,1⟩,⟨0,0,0,-1,1,-1,1,0⟩]
def rowB2 (i : ℕ) : Row := dataB2[i]!
theorem stepsB2 (i : ℕ) (hi : i<B2.length) :
    (label B2 i=2 → range4 (rowB2 i).i) ∧
    rowB2 (i+1)=move (decide (i%2=0)) (label B2 i) (rowB2 i) := by
  have ht : ∀ i : Fin 18, (label B2 i.val=2 → range4 (rowB2 i.val).i) ∧
      rowB2 (i.val+1)=move (decide (i.val%2=0)) (label B2 i.val) (rowB2 i.val) := by decide
  exact ht ⟨i,hi⟩

def W2 : List (Fin 3) := [0,1,0,1,2,0,1,2,0,2,1,0,2,0,2,1,0,2,0,2,1,0,2,1,0,1,2,0,1,0,1,2,0,2,0,1,2,0,2,1,0,2,1,0,1,0,2,1,0,1,0,2,1,0,1,2,0,1,2,0,2,0,1,2]

set_option maxHeartbeats 2000000 in
theorem form2 (x y : G) :
    prodFrom x y 0 W2 = (1) * ⁅prodFrom x y 0 A2,prodFrom x y 0 B2⁆ * (1)⁻¹ := by
  norm_num [W2,A2,B2,prodFrom,signPort,port,commutatorElement_def] <;> group

theorem close2 (nil : L G 7=⊥) (x y : G) : prodFrom x y 0 W2=1 := by
  have ord (X Y : G) : prodFrom X Y 0 A2 ∈ L G 2 :=
    in_gamma3 X Y A2 rowA2 (by decide) stepsA2 (by decide)
  have proj (X Y : G ⧸ L G 4) :
      prodFrom X Y 0 A2 = prodFrom X Y 0 B2 := by
    have a := prefix_eval (ls4quot_class4 G) X Y A2 rowA2 (by decide) stepsA2 A2.length (by omega)
    have b := prefix_eval (ls4quot_class4 G) X Y B2 rowB2 (by decide) stepsB2 B2.length (by omega)
    rw [HaarClass5TemplateClosure.path_full] at a b
    have e : rowA2 A2.length = rowB2 B2.length := by decide
    rw [e] at a
    exact a.trans b.symm
  rw [form2,(commute_words nil x y A2 B2 (ord x y)
    (proj _ _)).commutator_eq]
  group

def A3 : List (Fin 3) := [0,2,0,1,2,0,1,2,1,0,2,1]
def dataA3 : Array Row := #[⟨0,0,0,0,0,0,0,0⟩,⟨0,0,0,0,0,0,0,0⟩,⟨0,-1,0,0,0,0,0,0⟩,⟨0,-1,0,0,0,0,0,0⟩,⟨-1,-1,0,0,0,0,0,0⟩,⟨-1,0,-1,1,0,0,0,0⟩,⟨-1,0,-1,1,0,0,0,0⟩,⟨0,0,-1,0,0,0,0,0⟩,⟨0,-1,-1,0,1,0,0,0⟩,⟨1,-1,-1,-1,1,-1,1,0⟩,⟨1,-1,-1,-1,1,-1,1,0⟩,⟨1,0,0,-1,0,-1,0,0⟩,⟨0,0,0,-1,0,0,0,0⟩]
def rowA3 (i : ℕ) : Row := dataA3[i]!
theorem stepsA3 (i : ℕ) (hi : i<A3.length) :
    (label A3 i=2 → range4 (rowA3 i).i) ∧
    rowA3 (i+1)=move (decide (i%2=0)) (label A3 i) (rowA3 i) := by
  have ht : ∀ i : Fin 12, (label A3 i.val=2 → range4 (rowA3 i.val).i) ∧
      rowA3 (i.val+1)=move (decide (i.val%2=0)) (label A3 i.val) (rowA3 i.val) := by decide
  exact ht ⟨i,hi⟩

def B3 : List (Fin 3) := [2,1,0,2,1,2,1,0,2,1,0,2,0,1,2,0,2,0,1,2]
def dataB3 : Array Row := #[⟨0,0,0,0,0,0,0,0⟩,⟨0,1,0,0,0,0,0,0⟩,⟨-1,1,0,0,0,0,0,0⟩,⟨-1,1,0,0,0,0,0,0⟩,⟨-1,0,1,-1,-1,0,1,0⟩,⟨0,0,1,0,-1,0,0,0⟩,⟨0,-1,1,0,-2,0,0,1⟩,⟨1,-1,1,1,-2,1,-2,1⟩,⟨1,-1,1,1,-2,1,-2,1⟩,⟨1,0,2,1,-1,1,-1,0⟩,⟨0,0,2,-1,-1,0,0,0⟩,⟨0,0,2,-1,-1,0,0,0⟩,⟨0,-1,2,-1,-3,0,1,1⟩,⟨0,-1,2,-1,-3,0,1,1⟩,⟨-1,-1,2,-3,-3,1,4,1⟩,⟨-1,0,1,-2,-1,1,1,0⟩,⟨-1,0,1,-2,-1,1,1,0⟩,⟨-1,1,0,-1,0,1,-1,0⟩,⟨-1,1,0,-1,0,1,-1,0⟩,⟨0,1,0,-1,0,0,-1,0⟩,⟨0,0,0,-1,0,0,0,0⟩]
def rowB3 (i : ℕ) : Row := dataB3[i]!
theorem stepsB3 (i : ℕ) (hi : i<B3.length) :
    (label B3 i=2 → range4 (rowB3 i).i) ∧
    rowB3 (i+1)=move (decide (i%2=0)) (label B3 i) (rowB3 i) := by
  have ht : ∀ i : Fin 20, (label B3 i.val=2 → range4 (rowB3 i.val).i) ∧
      rowB3 (i.val+1)=move (decide (i.val%2=0)) (label B3 i.val) (rowB3 i.val) := by decide
  exact ht ⟨i,hi⟩

def W3 : List (Fin 3) := [0,2,0,1,2,0,1,2,1,0,2,1,2,1,0,2,1,2,1,0,2,1,0,2,0,1,2,0,2,0,1,2,1,2,0,1,2,1,0,2,1,0,2,0,2,1,0,2,0,2,1,0,2,0,1,2,0,1,2,1,2,0,1,2]

set_option maxHeartbeats 2000000 in
theorem form3 (x y : G) :
    prodFrom x y 0 W3 = (1) * ⁅prodFrom x y 0 A3,prodFrom x y 0 B3⁆ * (1)⁻¹ := by
  norm_num [W3,A3,B3,prodFrom,signPort,port,commutatorElement_def] <;> group

theorem close3 (nil : L G 7=⊥) (x y : G) : prodFrom x y 0 W3=1 := by
  have ord (X Y : G) : prodFrom X Y 0 A3 ∈ L G 2 :=
    in_gamma3 X Y A3 rowA3 (by decide) stepsA3 (by decide)
  have proj (X Y : G ⧸ L G 4) :
      prodFrom X Y 0 A3 = prodFrom X Y 0 B3 := by
    have a := prefix_eval (ls4quot_class4 G) X Y A3 rowA3 (by decide) stepsA3 A3.length (by omega)
    have b := prefix_eval (ls4quot_class4 G) X Y B3 rowB3 (by decide) stepsB3 B3.length (by omega)
    rw [HaarClass5TemplateClosure.path_full] at a b
    have e : rowA3 A3.length = rowB3 B3.length := by decide
    rw [e] at a
    exact a.trans b.symm
  rw [form3,(commute_words nil x y A3 B3 (ord x y)
    (proj _ _)).commutator_eq]
  group

theorem normalized (nil : L G 7=⊥) (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    ∃ k, 4≤k ∧ k≤46 ∧ Even k ∧ HasCycle x y k := by
  exact HaarReducedWalkCycle.fromWord x y hx hy hxy W0
    (by decide) (by decide) (by decide) (close0 nil x y)

theorem any_ports (nil : L G 7=⊥) (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ k, 4≤k ∧ k≤46 ∧ Even k ∧ HaarAnyPorts.HasPortCycle r s t k := by
  obtain ⟨a,b,c⟩ := HaarAnyPorts.as_three r s t hr ht hs
  obtain ⟨k,l,u,e,v⟩ := normalized nil (s*r⁻¹) (t*r⁻¹) a b c
  exact ⟨k,l,u,e,HaarAnyPorts.map_cycle r s t v⟩

end HaarClass7Parallel
#print axioms HaarClass7Parallel.close0
#print axioms HaarClass7Parallel.close1
#print axioms HaarClass7Parallel.close2
#print axioms HaarClass7Parallel.close3
#print axioms HaarClass7Parallel.any_ports
