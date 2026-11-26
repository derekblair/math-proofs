import RibbonP11JetUse
import RibbonStationaryWords
import RibbonP11Interfaces
import RibbonAffineFinal
namespace RibbonP11Adapters
open RibbonP11 RibbonDerived3 HaarClass4Structure
open RibbonP11Pair (bad two_charts)
open scoped commutatorElement
universe u

def Bad (v : F×F) : Prop := ∃ i : Fin 16, v=bad i

theorem dnil {G : Type u} [Group G] (m : RibbonDerivedTwo.D2 G) : DLS G 2=⊥ := by
  apply le_bot_iff.mp
  apply Subgroup.commutator_le.mpr
  intro a ha b hb
  exact Subgroup.mem_bot.mpr (RibbonStationaryWords.central m ha hb).commutator_eq

def normF {G : Type u} [Group G] {x y : G} {μ : G→*Fˣ} {τ : G→F}
    (co : RibbonStationaryChart.Aff μ τ)
    (n : Normalized (RingHom.id F) x y μ τ) {i : Fin 16}
    (e : ((μ x:F),(μ y:F))=bad i) : RibbonP11Pair.Coeffs x y i := by
  have xx : (μ x:F)=(bad i).1 := congrArg Prod.fst e
  have yy : (μ y:F)=(bad i).2 := congrArg Prod.snd e
  refine ⟨μ,τ,co,xx,yy,?_,?_⟩
  · rcases n with ⟨a,tx,_⟩ | ⟨a,_,tx,_⟩
    · have a' : (bad i).1≠1 := xx ▸ a
      simp [tx,a']
    · have a' : (bad i).1=1 := xx ▸ a
      simp [tx,a']
  · rcases n with ⟨a,_,ty⟩ | ⟨a,_,_,ty⟩
    · have a' : (bad i).1≠1 := xx ▸ a
      simp [ty,a']
    · have a' : (bad i).1=1 := xx ▸ a
      simp [ty,a']

theorem pair_cover : PairCover.{u} Bad := by
  intro G _ _ m x y μ ν τ σ _ co co' n n' h h' ne
  obtain ⟨i,ei⟩ := h
  obtain ⟨j,ej⟩ := h'
  have e : i≠j := fun e => ne (ei.trans (e ▸ ej.symm))
  have a := normF co n ei
  have b := normF co' n' ej
  apply Or.inr ∘ Or.inr ∘ Or.inr
  rcases lt_or_gt_of_ne e with lt|gt
  · exact two_charts (dnil m) x y i j lt a b
  · exact two_charts (dnil m) x y j i gt b a

theorem jet_cover : JetCover.{u} Bad := by
  intro G _ _ m x y μ τ _ co n h fresh
  obtain ⟨i,ei⟩ := h
  let da := (μ x:J).snd
  let db := (μ y:J).snd
  have ec : (TrivSqZeroExt.fst (μ x:J),TrivSqZeroExt.fst (μ y:J)) =
      ((bad i).1,(bad i).2) := ei
  have ecs := Prod.mk.inj ec
  have xx : (μ x:J).fst=(bad i).1 := ecs.1
  have yy : (μ y:J).fst=(bad i).2 := ecs.2
  have a : (μ x:J)=RibbonP11JetCalc.jet (bad i).1 da :=
    TrivSqZeroExt.ext xx rfl
  have b : (μ y:J)=RibbonP11JetCalc.jet (bad i).2 db :=
    TrivSqZeroExt.ext yy rfl
  refine Or.inr (Or.inr (Or.inr (RibbonP11JetCalc.one_jet (dnil m) x y i da db fresh
    ⟨μ,τ,co,a,b,?_,?_⟩)))
  · rcases n with ⟨nz,tx,_⟩ | ⟨z,_,tx,_⟩
    · have nz' : (bad i).1≠1 := xx ▸ nz
      simp [tx,nz',RibbonP11JetCalc.jet] <;> rfl
    · have z' : (bad i).1=1 := xx ▸ z
      simp [tx,z',RibbonP11JetCalc.jet] <;> rfl
  · rcases n with ⟨nz,_,ty⟩ | ⟨z,_,_,ty⟩
    · have nz' : (bad i).1≠1 := xx ▸ nz
      simp [ty,nz',RibbonP11JetCalc.jet] <;> rfl
    · have z' : (bad i).1=1 := xx ▸ z
      simp [ty,z',RibbonP11JetCalc.jet] <;> rfl

theorem meta_cover : MetaCover.{u} := by
  intro G _ _ m x y odd hx hy
  have h : IsMulCommutative (commutator G) := by
    rw [← Subgroup.top_lowerCentralSeries_one]
    refine ⟨⟨?_⟩⟩
    intro a b
    exact Subtype.ext (m a a.property b b.property).eq
  have C := RibbonAffine.finite_odd_metabelian_ribbon h x y odd hx hy
  exact C.imp_right (fun r => r.imp_right (fun s => s.imp_right Or.inl))

end RibbonP11Adapters
#print axioms RibbonP11Adapters.pair_cover
#print axioms RibbonP11Adapters.jet_cover
#print axioms RibbonP11Adapters.meta_cover
