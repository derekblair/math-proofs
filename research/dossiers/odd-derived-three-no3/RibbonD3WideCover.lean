import RibbonD3OddInterfaces
import RibbonD3WideOrbitCheckCore
import RibbonD3FieldPoint

namespace RibbonD3WideFinite
open RibbonD3Finite
open RibbonD3Orientation RibbonStationaryChart RibbonD3Stationary
open RibbonD3WordSelection RibbonD3VertexMates
open RibbonD3Field (chart)
open HaarClass4Structure RibbonP11 Ribbon5Bridge RibbonDerived3

universe u
variable {G : Type u} [Group G]

theorem chart_vertex (x y : G) (k : RibbonD3Field.Count) (i : Nat) :
    vertex x y k i = run x y ((chart k).start,1) ((chart k).ports.take i) := by
  have H := RibbonD3MateData.linked_all k
  change (chart k).key = _ ∧ (chart k).start = _ ∧ (chart k).ports.map Fin.val = _ at H
  have E : RibbonD3MateData.charts[k.val]! = mc k :=
    getElem!_pos RibbonD3MateData.charts k.val (idx k).isLt
  rw [E] at H
  have hs : (chart k).start=false := H.2.1.trans (data_valid k).1
  rw [vertex,RibbonD3FieldPoint.word_link,hs]
  rfl

def Witness (p : Nat) (x y : G) (l : Label × Nat × Nat) : Prop :=
  ∃ (μ : G→*(Jet p)ˣ) (τ : G→Jet p), Aff μ τ ∧ Normalized base x y μ τ ∧
    (paramsLabel (μ x:Jet p) (μ y:Jet p),(μ x:Jet p).snd.val,(μ y:Jet p).snd.val)=l

theorem witnessKeys {p : Nat} [Fact p.Prime] (x y : G) (l : Label × Nat × Nat)
    (h : Witness p x y l) (k : RibbonD3Field.Count) (i j : Fin 128)
    (E : vertex x y k i.val = vertex x y k j.val) :
    let v := l.1.inp l.2.1 l.2.2
    (row v k)[i.val]! = (row v k)[j.val]! := by
  obtain ⟨μ,τ,co,n,hl⟩ := h
  subst l
  rw [chart_vertex,chart_vertex] at E
  exact same_key μ τ co x y n k i j E

theorem certify {p q : Nat} [Fact p.Prime] [Fact q.Prime] (d3 : DLS G 3=⊥)
    (x y : G) (l m : Label × Nat × Nat)
    (h : Witness p x y l) (j : Witness q x y m)
    (c : Cert) (ok : good c (l.1.inp l.2.1 l.2.2) (m.1.inp m.2.1 m.2.2)) :
    LongGood x y := by
  apply Or.inr ∘ Or.inr ∘ Or.inr
  apply RibbonD3ChartCycles.from_chart d3 x y c.k
  intro a b E
  exact cert_sound ok a b (witnessKeys x y l h _ _ _ E) (witnessKeys x y m j _ _ _ E)

theorem affine_to_motion {p : Nat} [Fact p.Prime] (x y : G)
    (μ : G→*(Jet p)ˣ) (τ : G→Jet p) (co : Aff μ τ)
    (n : Normalized base x y μ τ) (l : Label) (da db m s : Nat)
    (lab : paramsLabel (μ x:Jet p) (μ y:Jet p)=l)
    (a : (μ x:Jet p).snd.val=da) (b : (μ y:Jet p).snd.val=db) :
    Witness p (act (motion m) x y).1 (act (motion m) x y).2 (acted l da db m s) := by
  obtain ⟨v,cv,nv⟩ := normalize_act (motion m) base lift_unit μ τ co x y n
  have H := scale_norm μ v cv (act (motion m) x y).1 (act (motion m) x y).2 nv (s:ZMod p)
  exact ⟨_,_,H.1,H.2,coefficients_after_motion μ x y l da db m s lab a b⟩

theorem triple_injective : Function.Injective Label.triple := by
  intro a b E
  cases a; cases b
  simp_all [Label.triple]

theorem acted_zero (l : Label) (m : Nat) : acted l 0 0 m 0 = (baseMotion l m,0,0) := by
  unfold acted baseMotion
  simp [scaleDig,acted]

theorem field_to_motion {p : Nat} [Fact p.Prime] (x y : G)
    (μ : G→*(ZMod p)ˣ) (τ : G→ZMod p) (co : Aff μ τ)
    (n : Normalized (RingHom.id (ZMod p)) x y μ τ) (l : Label) (m : Nat)
    (lab : RibbonOdd.Label p μ x y=l.triple) :
    Witness p (act (motion m) x y).1 (act (motion m) x y).2 (baseMotion l m,0,0) := by
  have H := lift_field μ τ co x y n
  rw [←acted_zero]
  apply affine_to_motion x y _ _ H.1 H.2 l 0 0 m 0
  · apply triple_injective
    exact lab
  · exact ZMod.val_zero
  · exact ZMod.val_zero

theorem jet_to_motion {p : Nat} [Fact p.Prime] (x y : G)
    (μ : G→*(Jet p)ˣ) (τ : G→Jet p) (co : Aff μ τ)
    (n : Normalized base x y μ τ) (i : B)
    (lab : RibbonOdd.JetLabel p μ x y=(getBad i).triple)
    (h : (μ x:Jet p).snd≠0 ∨ (μ y:Jet p).snd≠0) :
    ∃ d : Direction i, ∀ m s : Nat, Witness p (act (motion m) x y).1 (act (motion m) x y).2
      (acted (getBad i) (rawDir d).1 (rawDir d).2 m s) := by
  have ep : p=(getBad i).p := congrArg Prod.fst lab
  obtain ⟨s,d,hs⟩ := chooseDirection ep (μ x:Jet p).snd (μ y:Jet p).snd h
  let v := (Units.map (jScale s).toMonoidHom).comp μ
  let u := (jScale s) ∘ τ
  have H := scale_norm μ τ co x y n s
  refine ⟨d,fun m r => ?_⟩
  apply affine_to_motion x y v u H.1 H.2
  · apply triple_injective
    exact lab
  · exact congrArg Prod.fst hs
  · exact congrArg Prod.snd hs


def HavePairs : Prop := ∀ c : PP, ∃ w : Cert,
  good w ((pairLabel c).1.inp 0 0) ((pairLabel c).2.inp 0 0)

def HaveJets : Prop := ∀ c : JJ, let z := jetLabel c; ∃ w : Cert,
  good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2)

theorem from_pair_orbits (orbits : ∀ i : B, PairOrbit i) (checks : HavePairs) :
    RibbonD3Odd.PairCover.{u} Bad := by
  intro G _ _ dnil x y p q hp hq μ ν τ σ _ m n zx zy Bx By N
  letI : Fact p.Prime := ⟨RibbonD3Odd.prime_of_bad hp⟩
  letI : Fact q.Prime := ⟨RibbonD3Odd.prime_of_bad hq⟩
  obtain ⟨i,bi⟩ := Bx
  obtain ⟨j,bj⟩ := By
  have he : i≠j := fun e => N (bi.symm.trans (e ▸ bj))
  have cut {i j : B} (ij : i.val < j.val)
      (a : ∀ k : Nat, Witness p (act (motion k) x y).1 (act (motion k) x y).2
        (baseMotion (getBad i) k,0,0))
      (b : ∀ k : Nat, Witness q (act (motion k) x y).1 (act (motion k) x y).2
        (baseMotion (getBad j) k,0,0)) : LongGood x y := by
    obtain ⟨m,c,H⟩ := choosePair i j (orbits i j ij)
    obtain ⟨w,C⟩ := checks c
    apply longUnact (motion m)
    rcases H with H|H
    · rw [←H] at C
      exact certify dnil _ _ _ _ (a m) (b m) w C
    · rw [←H] at C
      exact certify dnil _ _ _ _ (b m) (a m) w C
  have L (i j : B) (ij : i.val < j.val) : PairResult i j := orbits i j ij
  rcases lt_or_gt_of_ne he with ij|ji
  · exact Or.inl (cut ij (fun k => field_to_motion x y μ τ m zx _ k bi.symm)
      (fun k => field_to_motion x y ν σ n zy _ k bj.symm))
  · obtain ⟨k,c,H⟩ := choosePair j i (L j i ji)
    obtain ⟨w,C⟩ := checks c
    have a := field_to_motion x y μ τ m zx (getBad i) k bi.symm
    have b := field_to_motion x y ν σ n zy (getBad j) k bj.symm
    apply Or.inl
    apply longUnact (motion k)
    rcases H with H|H
    · rw [←H] at C
      exact certify dnil _ _ _ _ b a w C
    · rw [←H] at C
      exact certify dnil _ _ _ _ a b w C

theorem from_jet_orbits (orbits : ∀ i : B, JetOrbit i) (checks : HaveJets) :
    RibbonD3Odd.JetCover.{u} Bad := by
  intro G _ _ dnil x y p hp μ τ _ co norm ⟨i,lab⟩ h
  letI : Fact p.Prime := ⟨RibbonD3Odd.prime_of_bad hp⟩
  obtain ⟨d,F⟩ := jet_to_motion x y μ τ co norm i lab.symm h
  obtain ⟨m,s,c,E⟩ := chooseJet i d (orbits i d)
  have A := F m s
  rw [E] at A
  obtain ⟨w,C⟩ := checks c
  exact Or.inl (longUnact (motion m) x y (certify dnil _ _ _ _ A A w C))

end RibbonD3WideFinite
