import N62A10PrivateSplit
import N62A10BActual
import N62NearCap

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13 Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

theorem a10_b_columns_bound
    (S X T : Finset V) (g h : V) (gt : g∉T) (ht : h∉T) (gh : g≠h)
    (tc : T.card=10) (se : S=insert g (insert h T))
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (iso : ∀ u ∈ ({g,h}:Finset V),∀ v∈S, ¬G u v)
    (cap : ∀ u∈T,ambientLoneRow G X u≤4)
    (b2 : bcnt G S X=2) (p q : V) (ps : p∈S) (qs : q∈S) (pq : p≠q) (edge : G p q)
    (uEq : S\(nearFrame G S X sym irr tf sc sf out upper).marks={p,q})
    (bf : ∀ z∈X, Bcol G S z → G p z ∧ G q z ∧ support G S z={p,q}) :
    dcnt G S X≤24 := by
  classical
  let F := nearFrame G S X sym irr tf sc sf out upper
  have pt : p∈T := by
    rw [se,mem_insert,mem_insert] at ps
    rcases ps with pe|pe|pt
    · exact False.elim (iso p (by simp [pe]) q qs edge)
    · exact False.elim (iso p (by simp [pe]) q qs edge)
    · exact pt
  have qt : q∈T := by
    rw [se,mem_insert,mem_insert] at qs
    rcases qs with qe|qe|qt
    · exact False.elim (iso q (by simp [qe]) p ps (sym edge))
    · exact False.elim (iso q (by simp [qe]) p ps (sym edge))
    · exact qt
  have marks : F.marks=S\({p,q}:Finset V) := by
    rw [←uEq,Finset.sdiff_sdiff_eq_self F.markSub]
  have own (u : V) (ut : u∈T) : (Dstar G F u).card≤3+(if u=p ∨ u=q then 1 else 0) := by
    have h := near_Dstar_lone_bound G F sym u
    have e := cap u ut
    by_cases hh : u∈({p,q}:Finset V)
    · have hu : u=p ∨ u=q := by simpa using hh
      simp [hu]
      omega
    · have hu : ¬(u=p ∨ u=q) := by simpa using hh
      have hm : u∈F.marks := by rw [marks]; exact mem_sdiff.mpr ⟨by simp [se,ut],hh⟩
      simp [hu]
      rw [if_pos hm] at h
      omega
  let B := weightedSet X (Bcol G S)
  have bc : B.card=2 := b2
  obtain ⟨x,y,xy,xyB⟩ := card_eq_two.mp bc
  have xB : x∈B := by simp [xyB]
  have yB : y∈B := by simp [xyB]
  obtain ⟨xx,bx⟩ := mem_filter.mp xB
  obtain ⟨yx,byc⟩ := mem_filter.mp yB
  obtain ⟨px,qx,sx⟩ := bf x xx bx
  obtain ⟨py,qy,sy⟩ := bf y yx byc
  have no (r : V) (rg : r∈({g,h}:Finset V)) :
      ¬(DoubleRel G F p r ∧ DoubleRel G F q r) := by
    rintro ⟨pr,qr⟩
    obtain ⟨a,ad,ea⟩ := drel_sym G F pr
    obtain ⟨b,bd,eb⟩ := drel_sym G F qr
    have rS : r∈S := by simp only [mem_insert,mem_singleton] at rg; rcases rg with rfl|rfl <;> simp [se]
    have rp : r≠p := fun eq => iso r rg q qs (eq ▸ edge)
    have rq : r≠q := fun eq => iso r rg p ps (eq ▸ sym edge)
    have diff (v w : V) (h1 : support G S v={p,q}) (h2 : support G S w={r,p} ∨ support G S w={r,q}) :
        v≠w := by
      intro eq
      have z : r∈support G S w := by
        rcases h2 with e|e <;> simp [e]
      rw [←eq,h1] at z
      simp [rp,rq] at z
    have ab : a≠b := by
      intro e
      have pu : p∈support G S a := by simp [ea]
      rw [e,eb] at pu
      simp [rp.symm,pq] at pu
    exact doubledB_no_common_double G sym irr tf S sc sf upper p q r x y a b
      ps qs rS xy (diff x a sx (Or.inl ea)) (diff x b sx (Or.inr eb))
      (diff y a sy (Or.inl ea)) (diff y b sy (Or.inr eb)) ab
      (Finset.disjoint_left.mp out xx) (Finset.disjoint_left.mp out yx)
      (Finset.disjoint_left.mp out (F.dblData a ad).1)
      (Finset.disjoint_left.mp out (F.dblData b bd).1)
      edge px qx py qy
      (near_double_lone_of_support G F ad (by simp [ea]))
      (near_double_lone_of_support G F bd (by simp [eb]))
      (near_double_lone_of_support G F ad (by simp [ea]))
      (near_double_lone_of_support G F bd (by simp [eb]))
      sx.le sy.le ea.le eb.le
  exact a10_b_actual_owner_bound G F sym irr sc sf out upper T g h gt ht gh tc se
    p q pt qt pq marks edge ⟨no g (by simp),no h (by simp)⟩ own

#print axioms a10_b_columns_bound
end Erdos151N62
