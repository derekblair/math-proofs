import RibbonAffineCore

namespace RibbonAffine
variable {K : Type*} [Field K]

def before (a b : Mono) : Prop :=
  a.1<b.1 ∨ (a.1=b.1 ∧ a.2.1<b.2.1)
instance (a b : Mono) : Decidable (before a b) := by unfold before; infer_instance

def ins (m : Mono) : List Mono → List Mono
  | [] => if m.2.2=0 then [] else [m]
  | p::l =>
    if m.1=p.1 ∧ m.2.1=p.2.1 then
      let k := m.2.2+p.2.2
      if k=0 then l else (m.1,m.2.1,k)::l
    else if before m p then if m.2.2=0 then p::l else m::p::l
    else p::ins m l

def nf (l : List Mono) : List Mono := l.foldr ins []

theorem pl_cons (a b : Kˣ) (m : Mono) (l : List Mono) :
    pl a b (m::l) = mon a b m + pl a b l := by simp [pl]

theorem pl_append (a b : Kˣ) (u v : List Mono) :
    pl a b (u++v) = pl a b u + pl a b v := by simp [pl]

theorem ins_sound (a b : Kˣ) (m : Mono) (l : List Mono) :
    pl a b (ins m l) = mon a b m + pl a b l := by
  induction l with
  | nil => by_cases e : m.2.2=0 <;> simp [ins,e,pl,mon]
  | cons p l ih =>
    by_cases h : m.1=p.1 ∧ m.2.1=p.2.1
    · have e := (if_pos h :
          (if m.1=p.1 ∧ m.2.1=p.2.1 then
            if m.2.2+p.2.2=0 then l else (m.1,m.2.1,m.2.2+p.2.2)::l
           else if before m p then if m.2.2=0 then p::l else m::p::l else p::ins m l) =
          (if m.2.2+p.2.2=0 then l else (m.1,m.2.1,m.2.2+p.2.2)::l))
      rw [ins,e]
      by_cases z : m.2.2+p.2.2=0
      · rw [if_pos z,pl_cons]
        unfold mon
        rw [←h.1,←h.2]
        have H : (m.2.2:K)+(p.2.2:K)=0 := by
          simpa using congrArg (fun g : ℤ => (g:K)) z
        rw [←add_assoc,← add_mul,H,zero_mul,zero_add]
      · rw [if_neg z,pl_cons,pl_cons]
        unfold mon
        simp only [Int.cast_add]
        rw [←h.1,←h.2]
        ring
    · by_cases b' : before m p
      · by_cases z : m.2.2=0 <;> simp [ins,h,b',z,pl_cons,mon]
      · simp only [ins,h,b',ite_false,pl_cons,ih]
        ring

theorem nf_sound (a b : Kˣ) (l : List Mono) : pl a b (nf l)=pl a b l := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [show nf (p::l)=ins p (nf l) from rfl,ins_sound,pl_cons,ih]

def negative (l : List Mono) : List Mono := l.map (fun t => (t.1,t.2.1,-t.2.2))

theorem negative_sound (a b : Kˣ) (l : List Mono) :
    pl a b (negative l) = -(pl a b l) := by
  induction l with
  | nil => simp [negative,pl]
  | cons p l ih =>
    simp only [negative,List.map_cons,pl_cons,mon,Int.cast_neg,neg_mul] at *
    rw [ih]; ring

def mulMono (u v : Mono) : Mono := (u.1+v.1,u.2.1+v.2.1,u.2.2*v.2.2)
def mulP (u v : List Mono) : List Mono := u.flatMap fun a => v.map (mulMono a)

theorem mon_mul (a b : Kˣ) (u v : Mono) :
    mon a b (mulMono u v)=mon a b u*mon a b v := by
  simp only [mon,mulMono,Int.cast_mul,zpow_add,Units.val_mul]
  ring

theorem pl_scal (a b : Kˣ) (u : Mono) (l : List Mono) :
    pl a b (l.map (mulMono u))=mon a b u * pl a b l := by
  induction l with
  | nil => simp [pl]
  | cons x xs ih =>
    simp only [List.map_cons,pl_cons,mon_mul,ih,mul_add]

theorem pl_mul (a b : Kˣ) (u v : List Mono) :
    pl a b (mulP u v)=pl a b u*pl a b v := by
  induction u with
  | nil => simp [mulP,pl]
  | cons x xs ih =>
    change pl a b (v.map (mulMono x) ++ mulP xs v)=_
    rw [pl_append,pl_scal,ih,pl_cons,add_mul]

theorem poly_eq (a b : Kˣ) (u v : List Mono) (H : nf u=nf v) : pl a b u=pl a b v := by
  rw [←nf_sound a b u,←nf_sound a b v,H]

def subUV (u v : ℤ) (l : List Mono) : List Mono :=
  l.map (fun m => (m.1*v-m.2.1*u,0,m.2.2))

theorem sub_sound (a : Kˣ) (u v : ℤ) (l : List Mono) :
    pl (a^v) (a^(-u)) l = pl a 1 (subUV u v l) := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    change pl (a^v) (a^(-u)) (m::l)=pl a 1 ((m.1*v-m.2.1*u,0,m.2.2)::subUV u v l)
    simp only [pl_cons,ih,mon,one_zpow,mul_one,←zpow_mul,←zpow_add]
    congr 2
    ring

end RibbonAffine
#print axioms RibbonAffine.poly_eq
#print axioms RibbonAffine.sub_sound
