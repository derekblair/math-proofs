import N63TenNoncubic
import N63ActualLink

namespace Erdos151H13
open Erdős151 Erdos151H12 Erdos151Ramsey
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V→V→Prop) [DecidableRel G] [DecidableRel C]

abbrev tenAdj (w : V) (i j : ↥(neighbors C w)) := G i.val j.val

theorem ten_link_degree_eq (w : V) (i : ↥(neighbors C w)) :
    Erdos151N63.fullDeg (tenAdj G C w) i = actualLinkDegree G C w i.val := by
  let F := Finset.univ.filter (tenAdj G C w i)
  let e : ↥(neighbors C w) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have he : F.map e = neighbors G i.val ∩ neighbors C w := by
    ext j
    simp only [F,e,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_inter,mem_neighbors]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨hx,(mem_neighbors C).mp x.property⟩
    · rintro ⟨hg,hc⟩
      exact ⟨⟨j,(mem_neighbors C).mpr hc⟩,hg,rfl⟩
  change F.card = _
  rw [←Finset.card_map e,he]
  rfl

theorem free13_of_ten_witness (w : V) (size : (neighbors C w).card=10)
    (wit : Erdos151N63.TenWitness (tenAdj G C w))
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41≤n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b)
    (Csym : ∀ {a b}, C a b → C b a) (coreNonlone : ∀ a b, C a b → ¬Lone G a b)
    (minC : ∀ v, C w v → 8 ≤ (neighbors C v).card)
    (maxG : ∀ v, (neighbors G v).card≤12) (ord : 63≤Fintype.card V) :
    ∃ T : Finset V, 13≤T.card ∧ Free (Forbidden G) (T : Set V) := by
  obtain ⟨x,y,S,xy,ng,az,si,pr⟩ := wit
  let e : ↥(neighbors C w) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let A := S.map e
  have cx := (mem_neighbors C).mp x.property
  have cy := (mem_neighbors C).mp y.property
  have aW : ∀ z∈A, C w z ∧ z≠x.val ∧ z≠y.val ∧ ¬G x.val z ∧ ¬G y.val z := by
    intro z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨h1,h2,h3,h4⟩ := az u hu
    exact ⟨(mem_neighbors C).mp u.property,
      fun h => h1 (Subtype.ext h),fun h => h2 (Subtype.ext h),h3,h4⟩
  have iA : Independent G A := by
    intro a ha b hb
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hb
    exact si i hi j hj
  apply free13_of_local_chart G C sym irr link R41 sub Csym coreNonlone x.val w y.val cx cy ng
    (fun h => xy (Subtype.ext h)) (minC _ cx) (minC _ cy) A aW iA ord (D:=36)
    (by have :=maxG x.val;have :=maxG w;have :=maxG y.val;omega) (maxG _)
  intro a b s al au bl bu hs
  rw [size] at au bu
  rw [ten_link_degree_eq G C w x,ten_link_degree_eq G C w y] at pr
  have ma := maxG w
  have ph := Erdos151N63.price_transfer 10 _ _ _ a b s pr al bl (by omega) (by omega) hs (by omega)
  have af : Erdos151N63.outerFloor a b s = outerFloor a b s := by
    unfold Erdos151N63.outerFloor outerFloor alphaFloorFour Erdos151N63.alphaFloor alphaFloor
    have ha : ¬9≤7-a-s := by omega
    have hb : ¬9≤7-b-s := by omega
    simp [ha,hb]
  rw [af] at ph
  rw [Finset.card_map]
  omega

theorem cubic_actual_ten (w : V) (size : (neighbors C w).card=10)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41≤n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b)
    (Csym : ∀ {a b}, C a b → C b a) (coreNonlone : ∀ a b, C a b → ¬Lone G a b)
    (minC : ∀ v, C w v → 8 ≤ (neighbors C v).card)
    (maxG : ∀ v, (neighbors G v).card≤12) (ord : 63≤Fintype.card V)
    (dmin : ∀ i : ↥(neighbors C w), 2≤actualLinkDegree G C w i.val)
    (dense : 30≤∑ i : ↥(neighbors C w), actualLinkDegree G C w i.val)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12) :
    ∀ i : ↥(neighbors C w), actualLinkDegree G C w i.val=3 := by
  intro i
  rw [←ten_link_degree_eq G C w i]
  apply Erdos151N63.cubic_of_no_ten_witness (tenAdj G C w)
    (by simpa using size) (fun _ _ => ⟨sym,sym⟩) (fun j => irr j.val)
    (fun v x y hx hy hxy => link w v.val x.val y.val
      (sub w _ ((mem_neighbors C).mp v.property))
      (sub w _ ((mem_neighbors C).mp x.property))
      (sub w _ ((mem_neighbors C).mp y.property)) hx hxy hy)
    (fun j => (ten_link_degree_eq G C w j).symm ▸ dmin j)
    (by simpa only [ten_link_degree_eq G C w] using dense)
  intro h
  obtain ⟨P,p,f⟩ := free13_of_ten_witness G C w size h sym irr link R41 sub Csym coreNonlone minC maxG ord
  have := upper P f
  omega

#print axioms cubic_actual_ten
end Erdos151H13
