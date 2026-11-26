import HaarP3FifthCertCore
import HaarClass5TemplateCycles

namespace HaarP3FifthCert
open HaarP3CollectCore HaarP3CollectActions HaarP3CollectSteps
open HaarAllNoncommuting HaarReducedWalkCycle HaarClass5DirTables HaarUniversal36

variable {G H : Type*} [Group G] [Group H]

theorem path_rows (M : Model G) (C : Cert) (ok : Valid M.P C) (i : ℕ) (hi : i≤64) :
    path M.x M.y (W C.t) i = ev M (row C i) := by
  induction i with
  | zero => rw [ok.1]; simp [path,ev,zeroGrid,ne_zero]
  | succ i ih =>
    have st := ok.2.2.2.1 ⟨i,by omega⟩
    change (if i%2=0 then
      (row C i=negStep M.P (HaarP3FifthCert.label C i) (row C (i+1)) ∧
        (HaarP3FifthCert.label C i=2 → rangeI (row C (i+1))))
      else (row C (i+1)=negStep M.P (HaarP3FifthCert.label C i) (row C i) ∧
        (HaarP3FifthCert.label C i=2 → rangeI (row C i)))) at st
    rw [path,ih (by omega)]
    change ev M _ * HaarHalfCollision.signPort M.x M.y i (HaarP3FifthCert.label C i) = _
    by_cases even : i%2=0
    · rw [if_pos even] at st
      have h := negStep_eval M ok.2.2.1 _ _ st.2
      rw [←st.1] at h
      simpa [HaarHalfCollision.signPort,even,h,mul_assoc] using
        (show (ev M (row C (i+1)) * (HaarHalfCollision.port M.x M.y (HaarP3FifthCert.label C i))⁻¹) *
          (HaarHalfCollision.port M.x M.y (HaarP3FifthCert.label C i)) = ev M (row C (i+1)) by
          simp [mul_assoc])
    · rw [if_neg even] at st
      rw [st.1,negStep_eval M ok.2.2.1 _ _ st.2]
      simp [HaarHalfCollision.signPort,even]

def SmallTail (r : Grid) : Prop :=
  (0≤r.n.u ∧ r.n.u<3) ∧ (0≤r.n.a ∧ r.n.a<3) ∧ (0≤r.n.z ∧ r.n.z<3)

def Separates (M : Model H) : Prop :=
  ∀ r s : Grid, SmallTail r → SmallTail s → ev M r=ev M s →
    (r.i-s.i)%3=0 ∧ (r.j-s.j)%3=0 ∧
    (r.i=s.i → r.j=s.j → (r.n.k-s.n.k)%3=0) ∧
    (r.i=s.i → r.j=s.j → r.n.k=s.n.k → r.n.u=s.n.u ∧ r.n.a=s.n.a ∧ r.n.z=s.n.z)

theorem lift_cycle (M : Model H) (C : Cert) (ok : Valid M.P C)
    (φ : G →* H) (x y : G) (hx : φ x=M.x) (hy : φ y=M.y)
    (closed : HaarHalfCollision.prodFrom x y 0 (W C.t)=1)
    (separates : Separates M) : HasCycle x y 64 := by
  apply HaarClass5TemplateCycles.cycle_of_vertices x y (W C.t) (W_len C.t) closed
  intro i j equal
  have side := congrArg Prod.fst equal
  change decide (i.val%2=1) = decide (j.val%2=1) at side
  have eqmod : i.val%2=j.val%2 := by
    by_cases e : i.val%2=1 <;> by_cases f : j.val%2=1 <;> simp [e,f] at side <;> omega
  have h := congrArg (fun z : Bool × G => φ z.2) equal
  change φ (path x y (W C.t) i.val)=φ (path x y (W C.t) j.val) at h
  rw [HaarClass5TemplateClosure.map_path,HaarClass5TemplateClosure.map_path,hx,hy,
    path_rows M C ok i.val i.isLt.le,path_rows M C ok j.val j.isLt.le] at h
  have hi : SmallTail (row C i.val) := (ok.2.2.2.2.1 i).2.2
  have hj : SmallTail (row C j.val) := (ok.2.2.2.2.1 j).2.2
  obtain ⟨I,J,K,T⟩ := separates _ _ hi hj h
  exact valid_pair C M.P ok i j eqmod I J K T

end HaarP3FifthCert
#print axioms HaarP3FifthCert.lift_cycle
