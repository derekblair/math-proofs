import MinimumEight
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod

open Finset
namespace BikovLocal

variable {V : Type*}

def Sym (G : V→V→Prop) : Prop := ∀ ⦃a b⦄, G a b → G b a
def Loopless (G : V→V→Prop) : Prop := ∀ a, ¬ G a a
def Sub (G H : V→V→Prop) : Prop := ∀ ⦃a b⦄, G a b → H a b
def Ramsey (G : V→V→Prop) : Prop :=
  ∀ c : V→V→Bool, (∀ a b, c a b=c b a) → ¬ Safe G c

def Removed (G : V→V→Prop) (x y a b : V) : Prop :=
  G a b ∧ ¬ (a=x ∧ b=y ∨ a=y ∧ b=x)

def Through (G : V→V→Prop) (x y z : V) : Prop := G x z ∧ G y z
def TwoThrough (G : V→V→Prop) (x y : V) : Prop :=
  ∃ u v, u≠v ∧ Through G x y u ∧ Through G x y v

def TriangleFreeLinks (G : V→V→Prop) : Prop :=
  ∀ v a b c, G v a → G v b → G v c → G a b → G a c → G b c → False

/-- If a deleted edge has at most one common neighbor, any coloring of
the deletion extends by choosing the color of this edge. -/
theorem extend_thin_edge (G : V→V→Prop) (sym : Sym G) (irr : Loopless G)
    (x y : V) (xy : G x y) (thin : ¬ TwoThrough G x y)
    (c : V→V→Bool) (cs : ∀ a b,c a b=c b a) (old : Safe (Removed G x y) c) :
    ∃ C : V→V→Bool, (∀ a b,C a b=C b a) ∧ Safe G C := by
  classical
  let D (a b : V) := (a=x ∧ b=y) ∨ (a=y ∧ b=x)
  have ds (a b : V) : D a b ↔ D b a := by
    constructor <;> rintro (⟨h,g⟩|⟨h,g⟩) <;> first | exact Or.inr ⟨g,h⟩ | exact Or.inl ⟨g,h⟩
  have xny : x≠y := fun eq=>irr x (eq.symm ▸ xy)
  let e : Bool := if h : ∃ z, Through G x y z then !c x (Classical.choose h) else false
  let C (a b : V) := if D a b then e else c a b
  have symC (a b) : C a b=C b a := by
    by_cases g : D a b
    · simp [C,g,(ds a b).mp g]
    · have gg : ¬D b a := fun h=>g ((ds a b).mpr h)
      simp [C,g,gg,cs a b]
  have good (z : V) (xz : G x z) (yz : G y z) :
      ¬ (C x y = C y z ∧ C y z = C z x) := by
    have nx : z≠x := fun h=>irr x (h ▸ xz)
    have ny : z≠y := fun h=>irr y (h ▸ yz)
    have ncY : ¬D y z := by simp [D,ny,nx,xny.symm]
    have ncX : ¬D z x := by simp [D,nx,ny]
    have nc : D x y := Or.inl ⟨rfl,rfl⟩
    have h : ∃ z, Through G x y z := ⟨z,xz,yz⟩
    have eq : Classical.choose h=z := by
      by_contra neq
      exact thin ⟨_,_,neq,Classical.choose_spec h,xz,yz⟩
    intro bad
    have impossible : (!c x z)=c x z := by
      have F := bad.1.trans bad.2
      simpa only [C,if_pos nc,if_neg ncX,e,dif_pos h,eq,cs z x] using F
    cases hc : c x z <;> simp [hc] at impossible
  have ordered (a b z : V) (d : D a b) (az : G a z) (bz : G b z) :
      ¬(C a b=C b z ∧ C b z=C z a) := by
    rcases d with ⟨h,g⟩|⟨h,g⟩ <;> subst a b
    · exact good z az bz
    · intro t
      apply good z bz az
      have t1 : C x y=C z x := (symC x y).trans (t.1.trans (symC x z))
      have t2 : C z x=C y z := (symC z x).trans (t.2.trans (symC z y))
      exact ⟨t1.trans t2,t2.symm⟩
  refine ⟨C,symC,?_⟩
  intro a b d ab bd da mm
  by_cases e1 : D a b
  · exact ordered a b d e1 (sym da) bd mm
  by_cases e2 : D b d
  · exact ordered b d a e2 (sym ab) da ⟨mm.2,mm.2.symm.trans mm.1.symm⟩
  by_cases e3 : D d a
  · exact ordered d a b e3 (sym bd) ab ⟨mm.2.symm.trans mm.1.symm,mm.1⟩
  exact old a b d ⟨ab,e1⟩ ⟨bd,e2⟩ ⟨da,e3⟩ (by simpa [C,e1,e2,e3] using mm)

noncomputable def directed [Fintype V] (G : V→V→Prop) : Finset (V×V) := by
  classical exact univ.filter (fun p=>G p.1 p.2)

lemma mem_directed [Fintype V] (G : V→V→Prop) (a b : V) :
    (a,b) ∈ directed G ↔ G a b := by classical simp [directed]

lemma directed_lt [Fintype V] (G H : V→V→Prop) (s : Sub G H)
    (a b : V) (ab : H a b) (no : ¬G a b) :
    (directed G).card < (directed H).card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
  · rintro ⟨x,y⟩ h
    exact (mem_directed H _ _).mpr (s ((mem_directed G _ _).mp h))
  · intro eq
    exact no ((mem_directed G a b).mp (eq ▸ (mem_directed H a b).mpr ab))

/-- Every finite K4-free Ramsey graph contains an edge-minimal Ramsey
core. Isolated vertices may remain in the ambient type, but each vertex
of its actual support has degree at least eight, and each core edge
has two distinct common neighbors. -/
theorem extract_core {V : Type*} [Fintype V]
    (G : V→V→Prop) (sym : Sym G) (irr : Loopless G) (tl : TriangleFreeLinks G)
    (r : Ramsey G) :
    ∃ C : V→V→Prop, Sub C G ∧ Sym C ∧ Loopless C ∧ TriangleFreeLinks C ∧ Ramsey C ∧
      (∃ a b,C a b) ∧
      (∀ v, (∃ w,C v w) → ∀ [Fintype {w : V // C v w}], 8≤Fintype.card {w : V // C v w}) ∧
      (∀ a b,C a b→TwoThrough C a b) := by
  classical
  have ex : ∃ n, ∃ C : V→V→Prop, Sub C G ∧ Sym C ∧ Ramsey C ∧ (directed C).card=n :=
    ⟨_,G,fun {_ _} h=>h,sym,r,rfl⟩
  obtain ⟨C,sub,cs,cr,cc⟩ := Nat.find_spec ex
  have cirr : Loopless C := fun a aa=>irr a (sub aa)
  have ctri : TriangleFreeLinks C := fun v a b c va vb vc ab ac bc=>
    tl v a b c (sub va) (sub vb) (sub vc) (sub ab) (sub ac) (sub bc)
  have less (H : V→V→Prop) (s : Sub H C) (hs : Sym H)
      (a b : V) (ab : C a b) (no : ¬H a b) : ¬Ramsey H := by
    intro hr
    have small := directed_lt H C s a b ab no
    have contra := Nat.find_min' ex (show ∃ C':V→V→Prop,
        Sub C' G ∧ Sym C' ∧ Ramsey C' ∧ (directed C').card=(directed H).card from
          ⟨H,fun {_ _} h=>sub (s h),hs,hr,rfl⟩)
    omega
  have colorable (H : V→V→Prop) (no : ¬Ramsey H) :
      ∃ c : V→V→Bool, (∀ a b,c a b=c b a) ∧ Safe H c := by
    by_contra! n
    apply no
    intro c cs h
    exact n c cs h
  have edge : ∃ a b,C a b := by
    by_contra! n
    have empty : Safe C (fun _ _ => false) := fun a b _ ab _ _ => False.elim (n a b ab)
    exact cr _ (fun _ _=>rfl) empty
  have degree : ∀ v, (∃ w,C v w) → ∀ [Fintype {w : V // C v w}], 8≤Fintype.card {w : V // C v w} := by
    intro v ⟨w,vw⟩ inst
    let H (a b : V) := a≠v ∧ b≠v ∧ C a b
    have s : Sub H C := by intro a b h; exact h.2.2
    have hs : Sym H := by intro a b h; exact ⟨h.2.1,h.1,cs h.2.2⟩
    have no : ¬H v w := fun h=>h.1 rfl
    exact bikov_degree_eight C cs cirr v (ctri v) cr (colorable H (less H s hs v w vw no))
  have book : ∀ a b,C a b→TwoThrough C a b := by
    intro a b ab
    by_contra thin
    let H := Removed C a b
    have s : Sub H C := by intro x y h; exact h.1
    have hs : Sym H := by
      intro x y h
      refine ⟨cs h.1,?_⟩
      rintro (⟨p,q⟩|⟨p,q⟩)
      · exact h.2 (Or.inr ⟨q,p⟩)
      · exact h.2 (Or.inl ⟨q,p⟩)
    have no : ¬H a b := fun h=>h.2 (Or.inl ⟨rfl,rfl⟩)
    obtain ⟨c,csym,ok⟩ := colorable H (less H s hs a b ab no)
    obtain ⟨c',cs',ok'⟩ := extend_thin_edge C cs cirr a b ab thin c csym ok
    exact cr c' cs' ok'
  exact ⟨C,sub,cs,cirr,ctri,cr,edge,degree,book⟩

#print axioms extend_thin_edge
#print axioms extract_core
end BikovLocal
