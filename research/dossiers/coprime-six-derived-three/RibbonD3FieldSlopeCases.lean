import RibbonD3FieldSlopeModular
import RibbonD3FieldBase

namespace RibbonD3Field
open RibbonAffine (pl)
open RibbonStationaryField (Branch)
variable {K : Type*} [Field K]

structure SlopeCertificate where
  geomIdx : Nat
  ints : IntCover
  mods : Array ModCover
  deriving Inhabited

def mod_for (bank : Array GeometryEntry) (B : Branch) (S : SlopeCertificate) (p : Nat) : Prop :=
  ∃ i : Fin S.mods.size, S.mods[i].p=p ∧ modValid bank B.u B.v B.p S.mods[i]
instance (bank : Array GeometryEntry) (B : Branch) (S : SlopeCertificate) (p : Nat) :
    Decidable (mod_for bank B S p) := by unfold mod_for; infer_instance

def certificateValid (bank : Array GeometryEntry) (B : Branch) (S : SlopeCertificate) : Prop :=
  S.geomIdx<bank.size ∧ bank[S.geomIdx]!.u=B.u ∧ bank[S.geomIdx]!.v=B.v ∧
    integerValid B.p bank[S.geomIdx]!.geom S.ints ∧
    (S.ints.primes.all fun p => decide (mod_for bank B S p))=true

instance (bank : Array GeometryEntry) (B : Branch) (S : SlopeCertificate) :
    Decidable (certificateValid bank B S) := by unfold certificateValid; infer_instance

theorem cert_sound (bank : Array GeometryEntry) (BV : BankValid bank)
    (B : Branch) (S : SlopeCertificate) (V : certificateValid bank B S)
    (t : Kˣ) (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (tn : t^n=1) (t1 : t≠1) (a1 : t^B.v≠1)
    (two : (2:K)≠0) (three : (3:K)≠0) (F : pl t 1 B.p=0) :
    (∃ k, Ordered (chart k) (t^B.v) (t^(-B.u))) ∨ ScalarPair (t^B.v) (t^(-B.u)) := by
  obtain ⟨l,u,v,I,J⟩ := V
  let j : Fin bank.size := ⟨S.geomIdx,l⟩
  let G := bank[j]
  have eq : bank[S.geomIdx]! = G := getElem!_pos bank S.geomIdx l
  rw [eq] at u v I
  have g : GeomValid G.geom B.u B.v := by simpa only [←u,←v] using BV j
  rcases integer_cover B.p G.geom S.ints B.u B.v g I t n odd no3 tn t1 two three F with H|⟨p,hp,P⟩
  · exact Or.inl ⟨_,H⟩
  obtain ⟨q,E,V⟩ := of_decide_eq_true (List.all_eq_true.mp J p hp)
  have PP : (S.mods[q].p:K)=0 := by rwa [E]
  exact mod_cover bank BV B.u B.v B.p S.mods[q] V t n odd no3 tn t1 a1 PP F

end RibbonD3Field
#print axioms RibbonD3Field.cert_sound
