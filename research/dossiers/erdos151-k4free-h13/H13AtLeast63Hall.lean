import N63CoreCertified
import HallAllMixed
namespace Erdős151.H13
open Erdos151H12 Erdos151H13 H13MixedComponents H13PetersenComponents
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem ramsey_free13_at_least63_of_hall_all (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41≤n → H10.TriangleIndependentTen (Fin n))
    (n63 : 63≤Fintype.card V) (hall : HallProjectionAll.{u})
    (ramsey : BikovLocal.Ramsey G) :
    ∃ T : Finset V, 13≤T.card ∧ Free (Forbidden G) (T : Set V) := by
  classical
  by_contra bad
  have deg (w : V) : (neighbors G w).card ≤ 12 := by
    by_contra hn
    have eq : (↑(neighbors G w) : Set V) = {u | G w u} := by
      ext u
      simp [neighbors]
    exact bad ⟨neighbors G w,by omega,by rw [eq]; exact neighborhood_free G sym link w⟩
  obtain ⟨C,sub,cs,ci,ct,cr,_,minC,two,minimal⟩ :=
    BikovLocal.extract_core_minimal G (fun {_ _} h=>sym h) irr
      (fun w a b c wa wb wc ab ac bc=>link w a b c wa wb wc ab bc ac) ramsey
  have min8 (w : V) (hw : (neighbors C w).Nonempty) : 8 ≤ (neighbors C w).card := by
    obtain ⟨v,hv⟩ := hw
    have h := minC w ⟨v,(mem_neighbors C).mp hv⟩
    simpa only [Fintype.card_subtype,neighbors] using h
  have twoC : TwoTriangles C := by
    intro u v uv
    obtain ⟨a,b,ne,ha,hb⟩ := two u v uv
    exact ⟨a,b,ne,ha.1,ha.2,hb.1,hb.2⟩
  have shapes := certified_tight_core63 G C sym irr link R41 sub cs ci ct cr minimal min8 twoC deg n63 bad
  apply nonRamsey_neutral_shapes_hall_all C cs ci ct hall _ cr
  · intro w hw
    rcases shapes w hw with h|⟨r,_,d⟩
    · exact Or.inl h
    · exact Or.inr ⟨r,d⟩

/-- Erdős #151's K₄-free H(n)=13 slice at n≥63 using R(3,10)≤41
and Hall's three-case locally Petersen recognition only. No
R(3,11)≤50 input is used in this stronger route. -/
theorem erdos151_k4free_H13_at_least63_of_hall_all (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41≤n → H10.TriangleIndependentTen (Fin n))
    (n63 : 63≤Fintype.card V) (hall : HallProjectionAll.{u})
    (H : TriangleIndependentAtLeast 13 V) :
    ∃ T : Finset V, T.card ≤ Fintype.card V-13 ∧
      ∀ Q, MaximalNontrivialClique G Q → ∃ x∈Q, x∈T :=
  k4free_transversal_from_ramsey_case G 13 sym irr link H
    (ramsey_free13_at_least63_of_hall_all G sym irr link R41 n63 hall)

#print axioms erdos151_k4free_H13_at_least63_of_hall_all
end Erdős151.H13
