import RibbonD3FieldScalar

namespace RibbonD3Field
open RibbonStationaryField (Id Poly Branch)
open RibbonAffine (pl prodP prodP_sound nf poly_eq)
variable {K : Type*} [Field K]

structure GeometryEntry where
  u : Int
  v : Int
  geom : SlopeGeom
  deriving Inhabited

def BankValid (bank : Array GeometryEntry) : Prop :=
  ∀ i : Fin bank.size, let e := bank[i]; GeomValid e.geom e.u e.v

inductive Outcome where
  | scalar (r a b : Nat)
  | reject (f : Poly) (w : Exclude)
  | compare (f : Poly) (gidx : Nat) (w : ModBlock)
  deriving Inhabited

def Outcome.poly : Outcome→Poly
  | .scalar r _ _ => rootPoly r
  | .reject f _ => f
  | .compare f _ _ => f

def Outcome.valid (bank : Array GeometryEntry) (u v : Int) (p : Nat) : Outcome→Prop
  | .scalar r a b => scalarPower p r a b u v ∧ (p,a,b)∈provisional
  | .reject f w => w.valid p f v
  | .compare f k w => k<bank.size ∧ bank[k]!.u=u ∧ bank[k]!.v=v ∧ blockValid p f bank[k]!.geom w
instance (bank : Array GeometryEntry) (u v : Int) (p : Nat) (O : Outcome) :
    Decidable (O.valid bank u v p) := by cases O <;> unfold Outcome.valid <;> infer_instance

theorem outcome_sound (bank : Array GeometryEntry) (BV : BankValid bank) (u v : Int)
    (p : Nat) (O : Outcome) (V : O.valid bank u v p)
    (t : Kˣ) (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (tn : t^n=1) (t1 : t≠1)
    (pivot : t^v≠1) (P : (p:K)=0) (F : pl t 1 O.poly=0) :
    (∃ k, Ordered (chart k) (t^v) (t^(-u))) ∨ ScalarPair (t^v) (t^(-u)) := by
  cases O with
  | scalar r a b => exact Or.inr (scalar_power_sound p r a b u v V.1 V.2 t P (linear_root r t F))
  | reject f w => exact False.elim (exclude p f v w V t n odd no3 tn pivot P F)
  | compare f k w =>
    obtain ⟨l,ku,kv,h⟩ := V
    let idx : Fin bank.size := ⟨k,l⟩
    let X := bank[idx]
    have eqn : bank[k]! = X := getElem!_pos bank k l
    rw [eqn] at ku kv h
    have b := block_sound X.geom X.u X.v (BV idx) p f w h t n odd no3 tn t1 P F
    rw [ku,kv] at b
    exact Or.inl ⟨_,b⟩

structure ModCover where
  p : Nat
  outcomes : List Outcome
  factor : Id
  deriving Inhabited

def modValid (bank : Array GeometryEntry) (u v : Int) (f : Poly) (C : ModCover) : Prop :=
  (C.outcomes.all fun o => decide (o.valid bank u v C.p))=true ∧
  C.factor.rhs=prodP (C.outcomes.map Outcome.poly) ∧ C.factor.valid f [] [] C.p
instance (bank : Array GeometryEntry) (u v : Int) (f : Poly) (C : ModCover) :
    Decidable (modValid bank u v f C) := by unfold modValid; infer_instance

theorem mod_cover (bank : Array GeometryEntry) (BV : BankValid bank) (u v : Int)
    (f : Poly) (C : ModCover) (CV : modValid bank u v f C)
    (t : Kˣ) (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (tn : t^n=1) (t1 : t≠1)
    (pivot : t^v≠1) (P : (C.p:K)=0) (F : pl t 1 f=0) :
    (∃ k, Ordered (chart k) (t^v) (t^(-u))) ∨ ScalarPair (t^v) (t^(-u)) := by
  have G := C.factor.sound f [] [] C.p CV.2.2 t F rfl rfl (by simpa using P)
  rw [CV.2.1,prodP_sound] at G
  obtain ⟨f,hF,W⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp G)
  obtain ⟨o,h,rfl⟩ := List.mem_map.mp hF
  exact outcome_sound bank BV u v C.p o (of_decide_eq_true (List.all_eq_true.mp CV.1 o h))
    t n odd no3 tn t1 pivot P W

end RibbonD3Field
#print axioms RibbonD3Field.mod_cover
