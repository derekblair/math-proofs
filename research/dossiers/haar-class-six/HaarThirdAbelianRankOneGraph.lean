import HaarThirdAbelianRankOneClosure
import HaarP3LayerGenModels
import HaarP3Class4Order
import HaarClass5TemplateCycles

namespace HaarThirdAbelianRankOneGraph
open HaarUniversal36 HaarHalfCollision HaarReducedWalkCycle HaarAllNoncommuting
open HaarClass4Table HaarClass4Normal HaarClass4Ports
open HaarThirdAbelianRankOneCert HaarThirdAbelianRankOneClosure HaarP3Class4Interpret HaarP3Class4Order
open HaarP3Class4Cases (Coeff lead rem4)
open HaarClass4Generate
open scoped commutatorElement
variable {G H : Type*} [Group G] [Group H]

theorem rows_eval (nil : L G 4=⊥) (x y : G) (t : Fin 3) (i : ℕ) (hi : i≤64) :
    path x y (W t) i = eval (make nil x y) (row t i) := by
  let M := make nil x y
  induction i with
  | zero => rw [HaarThirdAbelianRankOneCert.zero]; simp [path,eval,base,mid,HaarClass4Normal.tail]
  | succ i ih =>
    obtain ⟨rc,rd⟩ := steps t ⟨i,by omega⟩
    change (label (W t) i=2 → HaarP3Class4Collect.range4 (row t i).i) at rc
    change row t (i+1)=HaarP3Class4Collect.move (decide (i%2=0)) (label (W t) i) (row t i) at rd
    rw [path,ih (by omega),rd]
    have e := HaarP3Class4Collect.step_eval M (decide (i%2=0)) (label (W t) i) (row t i) rc
    simpa [M,make,signPort] using e.symm

theorem witness (ab : ∀ a b, a∈L G 2 → b∈L G 2 → Commute a b) (f : G →* H) (nil4 : L H 4=⊥)
    (x y : G) (t : Fin 3)
    (oc : 3∣orderOf (QuotientGroup.mk' (L H 2) (portC (f x) (f y))))
    (reject : ∀ a∈critical t, tailValue (make nil4 (f x) (f y)) a ≠ 1) :
    HasCycle x y 64 := by
  let M := make nil4 (f x) (f y)
  let φ := QuotientGroup.mk' (L H 2)
  have hm : HaarClass4Projection.KillsMid M φ := small_projection nil4 (f x) (f y)
  apply HaarClass5TemplateCycles.cycle_of_vertices x y (W t)
    (len t) (closes ab x y t)
  let v (i : Fin 64) := HaarClass5TemplateCycles.vertex x y (W t) i.val
  have no (i j : Fin 64) (ij : i.val<j.val) (eq : v i = v j) : False := by
    have ps := congrArg Prod.fst eq
    change decide (i.val%2=1) = decide (j.val%2=1) at ps
    have side_eq : i.val%2=j.val%2 := by
      by_cases a : i.val%2=1 <;> by_cases b : j.val%2=1 <;> simp [a,b] at ps <;> omega
    have h := congrArg (fun q : Bool × G => f q.2) eq
    change f (path x y (W t) i.val) = f (path x y (W t) j.val) at h
    rw [HaarClass5TemplateClosure.map_path,HaarClass5TemplateClosure.map_path,
      rows_eval nil4 _ _ _ _ (by omega),rows_eval nil4 _ _ _ _ (by omega)] at h
    let p := row t i.val
    let q := row t j.val
    let d := diff p q
    change eval M p=eval M q at h
    have ⟨ai,aj,ac⟩ := HaarClass4Projection.projections_of_equal M φ hm p q h
    have test := all_pairs t i j
    change j.val ≤ i.val ∨ i.val%2≠j.val%2 ∨ d.i%3≠0 ∨ d.j%3≠0 ∨
      (d.i=0 ∧ d.j=0 ∧ d.c%3≠0) ∨
      (d.i=0 ∧ d.j=0 ∧ d.c=0 ∧ tail d ∈ critical t) at test
    rcases test with v|v|v|v|⟨di,dj,v⟩|⟨di,dj,dc,dm⟩
    · omega
    · exact v side_eq
    · exact v (order_mod oc ai)
    · exact v (order_mod oc aj)
    · exact v (order_mod oc (ac di dj))
    · have e := HaarClass4Projection.equal_diff M p q di dj h
      apply reject (tail d) dm
      change d.i=0 at di
      change d.j=0 at dj
      change d.c=0 at dc
      change eval M d=1 at e
      simpa [tailValue,HaarThirdAbelianRankOneCert.tail,eval,di,dj,dc,mid,HaarClass4Normal.tail,mul_assoc] using e
  intro i j e
  by_contra hij
  have e' : v i = v j := e
  rcases lt_or_gt_of_ne (fun t => hij (Fin.ext t)) with lt|lt
  · exact no i j lt e'
  · exact no j i lt e'.symm

theorem accepted_nonzero {t : Fin 3} {axis : Fin 4} {j e : Fin 3}
    (h : accepted t axis j e = true) {a : Coeff} (ha : a∈critical t) :
    lead axis a%3≠0 ∨ rem4 axis j e a%3≠0 := by
  unfold accepted at h
  exact of_decide_eq_true (List.all_eq_true.mp h a ha)

theorem from_U (ab : ∀ a b, a∈L G 2 → b∈L G 2 → Commute a b) (f : G →* H) (nil4 : L H 4=⊥)
    (x y : G) (w : Fin 3) (j t e : Fin 3)
    (hm : let M := make nil4 (f x) (f y)
          orderOf M.a=3 ∧ M.v=M.u^j.val*M.a^t.val ∧ M.u^(3:ℕ)=M.a^e.val ∧
            M.b=M.a^j.val ∧ M.d=M.a^(j.val*j.val))
    (good : accepted w (firstAxis j) t e = true) : HasCycle x y 64 := by
  let X := f x
  let Y := f y
  let M := make nil4 X Y
  let φ := QuotientGroup.mk' (L H 3)
  obtain ⟨ha,hv,cu,hb,hd⟩ := hm
  have ah : M.a∈L H 3 := (tail_layers nil4 X Y).1
  have pa : φ M.a=1 := (QuotientGroup.eq_one_iff _).mpr ah
  have po : orderOf (φ M.u)=3 := pivot_order nil4 M.u X e.val ha ah cu
  have oc := c_order3 (portC X Y) X (layer_c X Y) po
  apply witness ab f nil4 x y w oc
  intro a mem z
  have nc := accepted_nonzero good mem
  have k := detect_U M φ j t e a ha pa (by rw [po]) hv hb hd cu z
  exact nc.elim (fun n => n k.1) (fun n => n k.2)

theorem from_V (ab : ∀ a b, a∈L G 2 → b∈L G 2 → Commute a b) (f : G →* H) (nil4 : L H 4=⊥)
    (x y : G) (w : Fin 3) (t e : Fin 3)
    (hm : let M := make nil4 (f x) (f y)
          orderOf M.d=3 ∧ M.u=M.d^t.val ∧ M.v^(3:ℕ)=M.d^e.val ∧ M.a=1 ∧ M.b=1)
    (good : accepted w 3 t e = true) : HasCycle x y 64 := by
  let X := f x
  let Y := f y
  let M := make nil4 X Y
  let φ := QuotientGroup.mk' (L H 3)
  obtain ⟨hd,hu,cv,ha,hb⟩ := hm
  have dh : M.d∈L H 3 := (tail_layers nil4 X Y).2.2
  have pd : φ M.d=1 := (QuotientGroup.eq_one_iff _).mpr dh
  have po : orderOf (φ M.v)=3 := pivot_order nil4 M.v Y e.val hd dh cv
  have oc := c_order3 (portC X Y) Y (layer_c X Y) po
  apply witness ab f nil4 x y w oc
  intro a mem z
  have nc := accepted_nonzero good mem
  have k := detect_V M φ t e a hd pd (by rw [po]) hu ha hb cv z
  exact nc.elim (fun n => n k.1) (fun n => n k.2)

theorem all_models (ab : ∀ a b, a∈L G 2 → b∈L G 2 → Commute a b)
    (f : G →* H) (nil4 : L H 4=⊥) (deep : L H 3≠⊥)
    (x y : G) (gen : Generates (f x) (f y))
    (size : Nat.card ((L H 2).map (QuotientGroup.mk' (L H 3)))=3) :
    HasCycle x y 64 := by
  obtain ⟨_,m⟩ := HaarP3LayerGen.models nil4 deep (f x) (f y) gen size
  rcases m with ⟨j,t,e,hm⟩ | ⟨t,e,hm⟩
  · obtain ⟨w,h⟩ := cover (firstAxis j) t e
    exact from_U ab f nil4 x y w j t e hm h
  · obtain ⟨w,h⟩ := cover 3 t e
    exact from_V ab f nil4 x y w t e hm h

end HaarThirdAbelianRankOneGraph
#print axioms HaarThirdAbelianRankOneGraph.all_models
