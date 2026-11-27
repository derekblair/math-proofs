import HaarClass4Projection

namespace HaarClass4Certificates
open HaarCycle HaarAllNoncommuting HaarClass4Normal HaarClass4Table HaarClass4Graph HaarClass4Projection

variable {G H K : Type*} [Group G] [Group H] [Group K]

theorem injective_of_ne (M : Data G) (T : ℕ → Row)
    (h : ∀ i j : Fin 32, i.val<j.val → side i=side j → eval M (T i.val) ≠ eval M (T j.val)) :
    Function.Injective (HaarClass4Graph.vert M T) := by
  intro i j e
  rcases lt_trichotomy i.val j.val with z | z | z
  · exfalso
    exact h i j z (congrArg Prod.fst e) (congrArg Prod.snd e)
  · exact Fin.ext z
  · exfalso
    exact h j i z (congrArg Prod.fst e).symm (congrArg Prod.snd e).symm

theorem ordinary_simple (M : Data G) (φ : G →* H) (ψ : G →* K)
    (hφ : KillsMid M φ) (hψ : KillsTail M ψ)
    (ord : ∀ n : ℤ, small n → (φ M.c)^n ≠ 1)
    (u : ψ M.u ≠ 1) (F : eval M unstable ≠ 1) (F' : eval M unstable' ≠ 1) :
    HasCycle M.x M.y 32 := by
  apply cycle_form (HaarClass4Graph.vert M ordinary) _ (ordinary_adj M)
  apply injective_of_ne
  intro i j lt sideEq equality
  have hs := separateOrd i j
  rcases hs with h | h | h
  · omega
  · exact h sideEq
  let p := ordinary i.val
  let q := ordinary j.val
  let r := diff p q
  have hv := projections_of_equal M φ hφ p q equality
  change ordinarySeparation r at h
  rcases h with a|b|⟨i0,j0,c⟩|⟨i0,j0,c0,u1,v0⟩|e|e
  · exact ord _ a hv.1
  · exact ord _ b hv.2.1
  · exact ord _ c (hv.2.2 i0 j0)
  · have er := equal_diff M p q i0 j0 equality
    change eval M r=1 at er
    have ez := congrArg ψ er
    exact u (by simpa [eval,mid,tail,i0,j0,c0,u1,v0,hψ.a,hψ.b,hψ.d] using ez)
  · have ei : r.i=0 := by rw [e]; rfl
    have ej : r.j=0 := by rw [e]; rfl
    have er := equal_diff M p q ei ej equality
    change eval M r = 1 at er
    rw [e] at er
    exact F er
  · have ei : r.i=0 := by rw [e]; rfl
    have ej : r.j=0 := by rw [e]; rfl
    have er := equal_diff M p q ei ej equality
    change eval M r = 1 at er
    rw [e] at er
    exact F' er

theorem conditional_simple (M : Data G) (φ : G →* H)
    (hφ : KillsMid M φ)
    (ord : ∀ n : ℤ, n%3≠0 → (φ M.c)^n ≠ 1)
    (F : M.c^3=M.u*M.v) (U : M.u^3=M.a*M.b) (A : M.a^3=1) :
    HasCycle M.x M.y 32 := by
  apply cycle_form (HaarClass4Graph.vert M conditional) _ (conditional_adj M F U A)
  apply injective_of_ne
  intro i j lt sideEq equality
  have hs := separateCond i j
  rcases hs with h | h | h
  · omega
  · exact h sideEq
  have hv := projections_of_equal M φ hφ (conditional i.val) (conditional j.val) equality
  rcases h with a|b|⟨i0,j0,c⟩
  · exact ord _ a hv.1
  · exact ord _ b hv.2.1
  · exact ord _ c (hv.2.2 i0 j0)

end HaarClass4Certificates

#print axioms HaarClass4Certificates.ordinary_simple
#print axioms HaarClass4Certificates.conditional_simple
