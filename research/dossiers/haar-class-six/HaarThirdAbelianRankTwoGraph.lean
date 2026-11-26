import HaarThirdAbelianRankTwoClosure
import HaarP3Class4Order
import HaarP3LayerGen

namespace HaarThirdAbelianRankTwoGraph
open HaarUniversal36 HaarHalfCollision HaarReducedWalkCycle HaarAllNoncommuting
open HaarClass4Table HaarClass4Normal HaarClass4Ports HaarClass4Generate
open HaarClass6RankTwoCert HaarThirdAbelianRankTwoClosure HaarP3Class4Order HaarP3LayerGen
variable {G H K : Type*} [Group G] [Group H] [Group K]

theorem rows_eval (nil : L G 4=⊥) (x y : G) (t : Fin 3) (i : ℕ) (hi : i≤64) :
    path x y (W t) i = eval (make nil x y) (row t i) := by
  let M := make nil x y
  induction i with
  | zero => rw [HaarClass6RankTwoCert.zero]; simp [path,eval,base,mid,HaarClass4Normal.tail]
  | succ i ih =>
    obtain ⟨rc,rd⟩ := steps t ⟨i,by omega⟩
    change (label (W t) i=2 → HaarP3Class4Collect.range4 (row t i).i) at rc
    change row t (i+1)=HaarP3Class4Collect.move (decide (i%2=0)) (label (W t) i) (row t i) at rd
    rw [path,ih (by omega),rd]
    have e := HaarP3Class4Collect.step_eval M (decide (i%2=0)) (label (W t) i) (row t i) rc
    simpa [M,make,signPort] using e.symm

def qvalue (M : Data H) (a : Coeff) : H :=
  HaarClass4Normal.tail M a.2.2.1 a.2.2.2.1 a.2.2.2.2

theorem witness (abel : ∀ a b : G, a ∈ L G 2 → b ∈ L G 2 → Commute a b) (f : G →* H) (nil4 : L H 4=⊥)
    (x y : G) (t : Fin 3) (q : H →* K)
    (oc : 3∣orderOf (QuotientGroup.mk' (L H 2) (portC (f x) (f y))))
    (kA : q (make nil4 (f x) (f y)).a=1)
    (kB : q (make nil4 (f x) (f y)).b=1)
    (kD : q (make nil4 (f x) (f y)).d=1)
    (indep : ∀ u v : ℤ, (q (portU (f x) (f y)))^u*(q (portV (f x) (f y)))^v=1 →
      u%3=0 ∧ v%3=0)
    (reject : ∀ a∈critical t, qvalue (make nil4 (f x) (f y)) a ≠ 1) :
    HasCycle x y 64 := by
  let M := make nil4 (f x) (f y)
  let φ := QuotientGroup.mk' (L H 2)
  have hm : HaarClass4Projection.KillsMid M φ := small_projection nil4 (f x) (f y)
  apply HaarClass5TemplateCycles.cycle_of_vertices x y (W t)
    (len t) (closes abel x y t)
  let v (i : Fin 64) := HaarClass5TemplateCycles.vertex x y (W t) i.val
  have no (i j : Fin 64) (ij : i.val<j.val) (eq : v i = v j) : False := by
    have ps := congrArg Prod.fst eq
    change decide (i.val%2=1) = decide (j.val%2=1) at ps
    have side_eq : i.val%2=j.val%2 := by
      by_cases a : i.val%2=1 <;> by_cases b : j.val%2=1 <;> simp [a,b] at ps <;> omega
    have h := congrArg (fun d : Bool × G => f d.2) eq
    change f (path x y (W t) i.val) = f (path x y (W t) j.val) at h
    rw [HaarClass5TemplateClosure.map_path,HaarClass5TemplateClosure.map_path,
      rows_eval nil4 _ _ _ _ (by omega),rows_eval nil4 _ _ _ _ (by omega)] at h
    let p := row t i.val
    let q' := row t j.val
    let d := diff p q'
    change eval M p=eval M q' at h
    have ⟨ai,aj,ac⟩ := HaarClass4Projection.projections_of_equal M φ hm p q' h
    have test := all_pairs t i j
    change j.val ≤ i.val ∨ i.val%2≠j.val%2 ∨ d.i%3≠0 ∨ d.j%3≠0 ∨
      (d.i=0 ∧ d.j=0 ∧ d.c%3≠0) ∨
      (d.i=0 ∧ d.j=0 ∧ d.c=0 ∧ (d.u%3≠0 ∨ d.v%3≠0)) ∨
      (d.i=0 ∧ d.j=0 ∧ d.c=0 ∧ d.u=0 ∧ d.v=0 ∧ HaarClass6RankTwoCert.tail d ∈ critical t) at test
    rcases test with v|v|v|v|⟨di,dj,v⟩|⟨di,dj,dc,dUV⟩|⟨di,dj,dc,du,dv,dm⟩
    · omega
    · exact v side_eq
    · exact v (HaarP3Class4Interpret.order_mod oc ai)
    · exact v (HaarP3Class4Interpret.order_mod oc aj)
    · exact v (HaarP3Class4Interpret.order_mod oc (ac di dj))
    · have e := HaarClass4Projection.equal_diff M p q' di dj h
      change eval M d=1 at e
      have dUV0 : (q (portU (f x) (f y)))^d.u * (q (portV (f x) (f y)))^d.v = 1 := by
        have eq := congrArg q e
        change q M.a=1 at kA
        change q M.b=1 at kB
        change q M.d=1 at kD
        have e' : (q M.u)^d.u * (q M.v)^d.v=1 := by
          simpa [eval,di,dj,dc,mid,HaarClass4Normal.tail,kA,kB,kD] using eq
        exact e'
      have ⟨eu,ev⟩ := indep _ _ dUV0
      exact dUV.elim (fun h => h eu) (fun h => h ev)
    · have e := HaarClass4Projection.equal_diff M p q' di dj h
      apply reject (HaarClass6RankTwoCert.tail d) dm
      change eval M d=1 at e
      simpa [qvalue,HaarClass6RankTwoCert.tail,eval,di,dj,dc,du,dv,mid,HaarClass4Normal.tail,mul_assoc] using e
  intro i j e
  by_contra hij
  have e' : v i = v j := e
  rcases lt_or_gt_of_ne (fun t => hij (Fin.ext t)) with lt|lt
  · exact no i j lt e'
  · exact no j i lt e'.symm

theorem rank_two (abel : ∀ a b : G, a ∈ L G 2 → b ∈ L G 2 → Commute a b) (f : G →* H) (nil4 : L H 4=⊥)
    (deep : L H 3≠⊥) (x y : G) (gen : Generates (f x) (f y))
    (q : H →* K)
    (oc : 3∣orderOf (QuotientGroup.mk' (L H 2) (portC (f x) (f y))))
    (kA : q (make nil4 (f x) (f y)).a=1)
    (kB : q (make nil4 (f x) (f y)).b=1)
    (kD : q (make nil4 (f x) (f y)).d=1)
    (indep : ∀ u v : ℤ, (q (portU (f x) (f y)))^u*(q (portV (f x) (f y)))^v=1 →
      u%3=0 ∧ v%3=0) : HasCycle x y 64 := by
  let M := make nil4 (f x) (f y)
  by_cases eq0 : M.a=M.b
  · by_cases eq1 : M.b=1
    · have neq2 : M.b≠M.d := by
        intro eq2
        have h := ls3_eq_tail_closure nil4 (f x) (f y) gen
        change L H 3=Subgroup.closure ({M.a,M.b,M.d} : Set H) at h
        rw [eq0,←eq2,eq1] at h
        apply deep
        apply le_bot_iff.mp
        rw [h]
        apply (Subgroup.closure_le _).mpr
        intro z hz
        simpa using hz
      refine witness abel f nil4 x y 2 q oc kA kB kD indep ?_
      intro a ha eq
      have ma : a=(0,0,0,1,-1) := by simpa [critical] using ha
      subst a
      apply neq2
      change qvalue M _=1 at eq
      have h : M.b*M.d⁻¹=1 := by simpa [qvalue,HaarClass4Normal.tail] using eq
      exact mul_inv_eq_one.mp h
    · refine witness abel f nil4 x y 1 q oc kA kB kD indep ?_
      intro a ha eq
      have ma : a=(0,0,0,1,0) := by simpa [critical] using ha
      subst a
      apply eq1
      change qvalue M _=1 at eq
      simpa [qvalue,HaarClass4Normal.tail] using eq
  · refine witness abel f nil4 x y 0 q oc kA kB kD indep ?_
    intro a ha eq
    have ma : a=(0,0,1,-1,0) := by simpa [critical] using ha
    subst a
    apply eq0
    change qvalue M _=1 at eq
    have h : M.a*M.b⁻¹=1 := by simpa [qvalue,HaarClass4Normal.tail] using eq
    exact mul_inv_eq_one.mp h

end HaarThirdAbelianRankTwoGraph
#print axioms HaarThirdAbelianRankTwoGraph.rank_two
