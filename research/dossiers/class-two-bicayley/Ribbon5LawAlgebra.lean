import Ribbon5LawWords

namespace Ribbon5Law
open scoped commutatorElement
open HaarUniversal36 HaarClass5Commute

variable {G : Type*} [Group G]

def Central (t : G) : Prop := ∀ g : G, Commute t g

private theorem central_mul {a b : G} (ca : Central a) (cb : Central b) :
    Central (a*b) := fun g => (ca g).mul_left (cb g)
private theorem central_inv {a : G} (ca : Central a) :
    Central a⁻¹ := fun g => (ca g).inv_left
private theorem central_pow {a : G} (ca : Central a) (n : ℕ) :
    Central (a^n) := fun g => (ca g).pow_left n

theorem upper_central (nil : L G 5=⊥) {g : G} (h : g∈L G 4) : Central g := by
  intro w
  apply commutatorElement_eq_one_iff_commute.mp
  have e := next h w
  rw [nil,Subgroup.mem_bot] at e
  exact e

private theorem mulL (a b c : G) (h : Commute a ⁅b,c⁆) : ⁅a*b,c⁆ = ⁅b,c⁆ * ⁅a,c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,h.eq,mul_inv_cancel_right]

private theorem mulR (a b c : G) (h : Commute b ⁅a,c⁆) : ⁅a,b*c⁆ = ⁅a,b⁆ * ⁅a,c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,mul_assoc ⁅a,b⁆,h.eq]
  group

private theorem invR (a b : G) (h : Commute ⁅a,b⁆ b) : ⁅a,b⁻¹⁆ = ⁅a,b⁆⁻¹ := by
  rw [commutatorElement_inv_right,←commutatorElement_inv, h.inv_left.inv_right.symm.eq]
  group

private theorem conjugation_layer {n : ℕ} (x g : G) (h : g ∈ L G n) :
    ⁅x,g⁆ ∈ L G (n+1) := by
  rw [←commutatorElement_inv]
  exact (L G (n+1)).inv_mem (next h x)

private theorem conjugation_split (x g : G) : x*g*x⁻¹=⁅x,g⁆*g := by
  unfold commutatorElement
  group

/-- The four mixed commutators are a common central element, and the two
weight-two conjugates commute modulo the center. -/
theorem common (nil : L G 5=⊥) (x y : G) :
    let q := Q x y
    let z := Z x y
    let u := V1 x y
    let v := V0 x y
    let t := ⁅v,q⁆
    Central t ∧ Central ⁅z,q⁆ ∧
      ⁅u,z⁆=t ∧ ⁅u,q⁆=t ∧ ⁅v,z⁆=t := by
  dsimp only
  let q := Q x y
  let z := Z x y
  let v := V0 x y
  let u := V1 x y
  let d := ⁅x⁻¹,q⁆
  let f := ⁅x⁻¹,v⁆
  let t := ⁅v,q⁆
  have qL : q∈L G 1 := next (Subgroup.mem_top y) x
  have dL : d∈L G 2 := conjugation_layer _ _ qL
  have vL : v∈L G 2 := conjugation_layer _ _ qL
  have fL : f∈L G 3 := conjugation_layer _ _ vL
  have zd : z=d*q := by
    change x⁻¹*q*x=d*q
    simpa only [inv_inv] using conjugation_split x⁻¹ q
  have uf : u=f*v := by
    change x⁻¹*v*x=f*v
    simpa only [inv_inv] using conjugation_split x⁻¹ v
  have tc : Central t := upper_central nil (comm_delta vL y x)
  have cfq : Commute f q := centralizes_commutator 3 nil fL y x
  have cfz : Commute f z := by
    have E : z = ⁅x⁻¹*y*x,x⁆ := by
      change x⁻¹*⁅y,x⁆*x= _
      simpa only [inv_inv,inv_mul_cancel,one_mul] using conjugate_commutatorElement y x x⁻¹
    rw [E]
    exact centralizes_commutator 3 nil fL _ _
  have cdv : Commute d v := by
    have H := (centralizes_triple nil dL y x y).inv_right
    change Commute d ⁅y,⁅y,x⁆⁆
    simpa only [commutatorElement_inv] using H
  change Central t ∧ Central ⁅z,q⁆ ∧ ⁅u,z⁆=t ∧ ⁅u,q⁆=t ∧ ⁅v,z⁆=t
  have vz : ⁅v,z⁆=t := by
    rw [zd,mulR v d q (tc d).symm,cdv.symm.commutator_eq,one_mul]
  have uz : ⁅u,z⁆=t := by
    rw [uf,mulL f v z (by rw [vz]; exact (tc f).symm),cfz.commutator_eq,mul_one,vz]
  have uq : ⁅u,q⁆=t := by
    rw [uf,mulL f v q (tc f).symm,cfq.commutator_eq,mul_one]
  have zq : ⁅z,q⁆=⁅d,q⁆ := by
    rw [zd,mulL d q q (by simp),commutatorElement_self,one_mul]
  exact ⟨tc,by rw [zq]; exact upper_central nil (comm_delta dL y x),uz,uq,vz⟩

theorem comm_word_power (z q u v t : G)
    (ct : Central t) (czq : Central ⁅z,q⁆)
    (uz : ⁅u,z⁆=t) (uq : ⁅u,q⁆=t) (vz : ⁅v,z⁆=t) (vq : ⁅v,q⁆=t) :
    ⁅(u*z^2)*(v*q^2),(z*q)⁻¹⁆ = (⁅u*z^2,z⁻¹⁆)^4 := by
  let s := ⁅z,q⁆
  let r := z*q
  have qt : ⁅q,z⁆=s⁻¹ := (commutatorElement_inv z q).symm
  have zr : ⁅z,r⁆=s := by
    change ⁅z,z*q⁆=s
    rw [mulR z z q (czq z).symm,commutatorElement_self,one_mul]
  have qr : ⁅q,r⁆=s⁻¹ := by
    change ⁅q,z*q⁆=s⁻¹
    rw [mulR q z q (by simp),commutatorElement_self,mul_one,qt]
  have ur : ⁅u,r⁆=t*t := by
    change ⁅u,z*q⁆=t*t
    rw [mulR u z q (by rw [uq]; exact (ct z).symm),uz,uq]
  have vr : ⁅v,r⁆=t*t := by
    change ⁅v,z*q⁆=t*t
    rw [mulR v z q (by rw [vq]; exact (ct z).symm),vz,vq]
  have zzr : ⁅z^2,r⁆=s^2 := by
    exact ((show Commute z ⁅z,r⁆ from zr ▸ (czq z).symm).commutatorElement_pow_left 2).symm.trans
      (congrArg (·^2) zr)
  have qqr : ⁅q^2,r⁆=(s⁻¹)^2 := by
    have h : Commute q ⁅q,r⁆ := by rw [qr]; exact ((czq q).inv_left).symm
    exact (h.commutatorElement_pow_left 2).symm.trans (congrArg (·^2) qr)
  have wr : ⁅(u*z^2)*(v*q^2),r⁆=t^4 := by
    have A : ⁅u*z^2,r⁆=s^2*(t*t) := by
      rw [mulL _ _ _ (by rw [zzr]; exact ((czq u).pow_left 2).symm),zzr,ur]
    have B : ⁅v*q^2,r⁆=(s⁻¹)^2*(t*t) := by
      rw [mulL _ _ _ (by rw [qqr]; exact ((czq v).inv_left.pow_left 2).symm),qqr,vr]
    have cB : Central ⁅v*q^2,r⁆ := by
      rw [B]
      exact central_mul (central_pow (central_inv czq) _) (central_mul ct ct)
    rw [mulL _ _ _ (cB _).symm,A,B]
    have swap : (t*t)*s^2=s^2*(t*t) := ((central_mul ct ct) (s^2)).eq
    calc
      _ = (s⁻¹)^2 * (((t*t)*s^2)*(t*t)) := by simp only [mul_assoc]
      _ = ((s⁻¹)^2*s^2)*((t*t)*(t*t)) := by
        rw [swap]
        simp only [mul_assoc]
      _ = t^4 := by rw [inv_pow,inv_mul_cancel,one_mul,
          show (4:Nat)=2+2 from rfl,pow_add,pow_two]
  have us : ⁅u*z^2,z⁆=t := by
    have E : ⁅z^2,z⁆=1 := ((Commute.refl z).pow_left 2).commutator_eq
    rw [mulL _ _ _ (by rw [E]; exact Commute.one_right _),E,one_mul,uz]
  change ⁅(u*z^2)*(v*q^2),r⁻¹⁆ = (⁅u*z^2,z⁻¹⁆)^4
  rw [invR _ _ (by rw [wr]; exact (ct r).pow_left 4),wr,invR _ _ (by rw [us]; exact ct z),us,inv_pow]

theorem word26_value (nil : L G 5=⊥) (x y : G) :
    trace x y false word26 = ⁅V0 x y,Q x y⁆⁻¹ := by
  obtain ⟨ct,_,uz,_,_⟩ := common nil x y
  let u := V1 x y
  let z := Z x y
  let t := ⁅V0 x y,Q x y⁆
  have z2 : ⁅z^2,z⁆=1 := ((Commute.refl z).pow_left 2).commutator_eq
  have E : ⁅u*z^2,z⁆=t := by
    rw [mulL _ _ _ (by rw [z2]; exact Commute.one_right _),z2,one_mul]
    exact uz
  rw [rewrite26]
  change ⁅u*z^2,z⁻¹⁆=t⁻¹
  rw [invR _ _ (by rw [E]; exact ct z),E]

theorem word26_layer (nil : L G 5=⊥) (x y : G) :
    trace x y false word26 ∈ L G 4 := by
  rw [word26_value nil]
  have q : Q x y∈L G 1 := next (Subgroup.mem_top y) x
  have v : V0 x y∈L G 2 := conjugation_layer _ _ q
  exact (L G 4).inv_mem (comm_delta v y x)

theorem word26_central (nil : L G 5=⊥) (x y : G) : Central (trace x y false word26) :=
  upper_central nil (word26_layer nil x y)

theorem law (nil : L G 5=⊥) (x y : G) :
    trace x y false word32 = (trace x y false word26)^4 := by
  obtain ⟨ct,czq,uz,uq,vz⟩ := common nil x y
  rw [rewrite32,rewrite26]
  exact comm_word_power _ _ _ _ _ ct czq uz uq vz rfl

end Ribbon5Law
#print axioms Ribbon5Law.law
#print axioms Ribbon5Law.word26_central
