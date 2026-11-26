import RibbonOrderThreeCert
import RibbonP11Adapters

namespace RibbonOrderThree
open RibbonStationaryWord RibbonP11Charts RibbonStationaryChart Ribbon5Bridge RibbonDerived3
open HaarClass4Structure HaarClass4Ports

variable {G R K : Type*} [Group G] [CommRing R] [Field K]
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def mapPt (f : R→+*K) (s : Flat R) : Flat K := (s.1,f s.2.1,f s.2.2)

theorem map_step (f : R→+*K) (a ai b bi u v : R) (s : Flat R) (p : P) :
    mapPt f (flatStep a ai b bi u v s p) =
      flatStep (f a) (f ai) (f b) (f bi) (f u) (f v) (mapPt f s) p := by
  rcases s with ⟨s,q,t⟩
  cases s <;> fin_cases p <;> simp [mapPt,flatStep]

theorem map_fold (f : R→+*K) (a ai b bi u v : R) (s : Flat R) (w : List P) :
    mapPt f (w.foldl (flatStep a ai b bi u v) s) =
      w.foldl (flatStep (f a) (f ai) (f b) (f bi) (f u) (f v)) (mapPt f s) := by
  induction w generalizing s with
  | nil => rfl
  | cons p l ih => simp only [List.foldl_cons,ih,map_step]

theorem map_position (f : R→+*K) (a ai b bi u v : R) (s : Spec) (i : Nat) :
    mapPt f (flatPosition a ai b bi u v s i) =
      flatPosition (f a) (f ai) (f b) (f bi) (f u) (f v) s i := by
  unfold flatPosition
  rw [map_fold]
  simp only [mapPt,map_one,map_zero]

theorem mapPt_inj (f : R→+*K) (hinj : Function.Injective f) :
    Function.Injective (mapPt f) := by
  intro s t h
  change (s.1,f s.2.1,f s.2.2)=(t.1,f t.2.1,f t.2.2) at h
  have H := Prod.mk.inj h
  have T := Prod.mk.inj H.2
  exact Prod.ext H.1 (Prod.ext (hinj T.1) (hinj T.2))

theorem inputs_prime : ∀ i : Fin 28, (inputs i).p.Prime := by decide +kernel
theorem invert_inputs : ∀ i : Fin 28,
    (digit (inputs i).p (inputs i).a) * (digit (inputs i).p (inputs i).a)^((inputs i).p-2)=1 ∧
    (digit (inputs i).p (inputs i).b) * (digit (inputs i).p (inputs i).b)^((inputs i).p-2)=1 := by decide +kernel

theorem joint (dnil : DLS G 2=⊥) (x y : G)
    (o : orderOf (QuotientGroup.mk' (LS G 2) (portC x y))=3)
    (i : Fin 28)
    (μ : G→*Kˣ) (τ : G→K) (co : Aff μ τ)
    (f : ZMod (inputs i).p →+* K)
    (ax : f (digit (inputs i).p (inputs i).a)=(μ x:K))
    (byy : f (digit (inputs i).p (inputs i).b)=(μ y:K))
    (tx : f (coeffX (inputs i).p (inputs i).a)=τ x)
    (ty : f (coeffY (inputs i).p (inputs i).a)=τ y) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  let z := inputs i
  let k := wid z.word
  letI : Fact z.p.Prime := ⟨inputs_prime i⟩
  let chart (p : Fin 64) := (lowKey z.word p,affPt z.p z.a z.b k p)
  apply from_state dnil k x y chart
  · intro p q e
    apply Prod.ext (projected_sound x y z.word p q o e)
    have h := invert_inputs i
    have ma : (↑(μ x)⁻¹:K)=f ((digit z.p z.a)^(z.p-2)) :=
      RibbonP11Pair.inv_unit_of _ _ (by rw [←ax,←map_mul,h.1,map_one])
    have mb : (↑(μ y)⁻¹:K)=f ((digit z.p z.b)^(z.p-2)) :=
      RibbonP11Pair.inv_unit_of _ _ (by rw [←byy,←map_mul,h.2,map_one])
    apply mapPt_inj f f.injective
    change mapPt f (affPt z.p z.a z.b k p) = mapPt f (affPt z.p z.a z.b k q)
    have aa : f (digit z.p z.a)=(μ x:K) := ax
    have bb : f (digit z.p z.b)=(μ y:K) := byy
    have t1 : f (coeffX z.p z.a)=τ x := tx
    have t2 : f (coeffY z.p z.a)=τ y := ty
    simp only [affPt,map_position,aa,bb,t1,t2,←ma,←mb]
    exact flatPosition_same μ τ co x y (spec k) p.val q.val e
  · intro p q lt e
    exact both_checked (all_inputs i) p q lt (congrArg Prod.fst e) (congrArg Prod.snd e)

end RibbonOrderThree
#print axioms RibbonOrderThree.joint
