import LabelCycle
import LinkLift
import Mathlib.Data.Fintype.EquivFin

namespace BikovLocal

/-- Every edge coloring of a triangle-free seven-vertex link extends. -/
theorem fin7_spokes (R : F7→F7→Prop)
    (sym : ∀ ⦃a b⦄, R a b → R b a) (irr : ∀ a, ¬ R a a)
    (tri : ∀ a b c, R a b → R a c → R b c → False)
    (c : F7→F7→Bool) (csym : ∀ a b, c a b=c b a) :
    ∃ f : F7→Bool, ∀ a b, R a b → ¬ (f a=c a b ∧ f b=c a b) := by
  classical
  rcases classify_walk R sym irr tri with ⟨f,bip⟩|⟨k,K,σ,geom⟩
  · exact ⟨f,fun a b e h=>bip e (h.1.trans h.2.symm)⟩
  let S (i j : F7) := R (σ i) (σ j)
  have ordered_suff (f : Nat→Bool)
      (check : ∀ i j : F7, i<j → S i j →
        ¬(f i.val=c (σ i) (σ j) ∧ f j.val=c (σ i) (σ j))) :
      ∃ f : F7→Bool, ∀ a b, R a b → ¬ (f a=c a b ∧ f b=c a b) := by
    refine ⟨fun a=>f (σ.symm a).val,?_⟩
    intro a b h hh
    have E : S (σ.symm a) (σ.symm b) := by simpa [S] using h
    rcases lt_trichotomy (σ.symm a) (σ.symm b) with l|e|r
    · apply check _ _ l E
      simpa using hh
    · exact irr a ((σ.symm.injective e).symm ▸ h)
    · apply check _ _ r (sym E)
      rw [and_comm]
      simpa [csym b a] using hh
  let lab (e : E) := c (σ (Fin.ofNat 7 e.1)) (σ (Fin.ofNat 7 e.2))
  rcases K with rfl|rfl
  · let g (e : E) := decide (S (Fin.ofNat 7 e.1) (Fin.ofNat 7 e.2))
    have tf (i j k : Nat) (ij : i<j) (jk : j<k) (ks : k<7) :
        ¬(g (i,j)=true ∧ g (i,k)=true ∧ g (j,k)=true) := by
      intro h
      simp only [g,decide_eq_true_eq] at h
      exact tri _ _ _ h.1 h.2.1 h.2.2
    have ofV (i : F7) : Fin.ofNat 7 i.val=i := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt i.isLt
    have fix : ∀ e∈c5,g e=true := by
      intro ⟨i,j⟩ eg
      obtain ⟨ij,jb⟩ := c5_mem_bound _ eg
      let iv : F7 := ⟨i,lt_trans ij jb⟩
      let jv : F7 := ⟨j,jb⟩
      obtain ⟨j5,cy⟩ := (c5_class iv jv ij).mp eg
      have co := (geom iv jv ij j5).mpr cy
      have g0 : (Fin.ofNat 7 i)=iv := ofV iv
      have g1 : (Fin.ofNat 7 j)=jv := ofV jv
      change decide (S (Fin.ofNat 7 i) (Fin.ofNat 7 j))=true
      rw [g0,g1,decide_eq_true_eq]
      exact co
    obtain ⟨f,ff⟩ := c5_arbitrary g lab tf fix
    apply ordered_suff f
    intro i j ij e
    have mem : (i.val,j.val)∈c5 ∨ (i.val,j.val)∈extra := by
      by_cases h : j.val<5
      · exact Or.inl ((c5_class i j ij).mpr ⟨h,(geom i j ij h).mp e⟩)
      · exact Or.inr ((extra_class i j ij).mpr (by omega))
    have yes : g (i.val,j.val)=true := by simpa [g,ofV] using e
    simpa [lab,ofV] using ff _ mem yes
  · obtain ⟨f,ff⟩ := c7_extends lab
    apply ordered_suff f
    intro i j ij e
    have mem : (i.val,j.val)∈c7 := (c7_class i j ij).mpr ((geom i j ij j.isLt).mp e)
    have ofV (i : F7) : Fin.ofNat 7 i.val=i := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt i.isLt
    simpa [lab,ofV] using ff _ mem

/-- Isolate padding from an arbitrary finite domain into the seven-slot model. -/
theorem small_spokes {V : Type*} [Fintype V] (bound : Fintype.card V≤7)
    (R : V→V→Prop) (sym : ∀ ⦃a b⦄, R a b→R b a) (irr : ∀ a,¬R a a)
    (tri : ∀ a b c,R a b→R a c→R b c→False)
    (c : V→V→Bool) (csym : ∀ a b,c a b=c b a) :
    ∃ f : V→Bool, ∀ a b, R a b → ¬(f a=c a b ∧ f b=c a b) := by
  classical
  let E (x : V) : F7 := ((Fintype.equivFin V) x).castLE bound
  have inj : Function.Injective E := by
    intro a b h
    apply (Fintype.equivFin V).injective
    exact Fin.ext (congrArg (fun i : F7=>i.val) h)
  let P (i j : F7) := ∃ a b, E a=i ∧ E b=j ∧ R a b
  let C (i j : F7) := decide (∃ a b, E a=i ∧ E b=j ∧ c a b=true)
  have ps : ∀ ⦃i j⦄,P i j→P j i := by
    intro i j ⟨a,b,ha,hb,r⟩
    exact ⟨b,a,hb,ha,sym r⟩
  have pi : ∀ i,¬P i i := by
    intro i ⟨a,b,ha,hb,e⟩
    have eq := inj (ha.trans hb.symm)
    exact irr a (eq.symm ▸ e)
  have pt : ∀ i j k,P i j→P i k→P j k→False := by
    intro i j k ⟨a,b,ha,hb,r⟩ ⟨a',d,ha',hd,s⟩ ⟨b',d',hb',hd',t⟩
    have aeq := inj (ha'.trans ha.symm)
    have beq := inj (hb'.trans hb.symm)
    have deq := inj (hd'.trans hd.symm)
    subst a' b' d'
    exact tri _ _ _ r s t
  have Cs : ∀ i j,C i j=C j i := by
    intro i j
    have H : (∃ a b, E a=i ∧ E b=j ∧ c a b=true) ↔
             (∃ a b, E a=j ∧ E b=i ∧ c a b=true) := by
      constructor <;> rintro ⟨a,b,ha,hb,h⟩ <;> exact ⟨b,a,hb,ha,(csym b a).trans h⟩
    by_cases hh : ∃ a b, E a=i ∧ E b=j ∧ c a b=true
    · exact (decide_eq_true hh).trans (decide_eq_true (H.mp hh)).symm
    · have hh' := fun hp=>hh (H.mpr hp)
      exact (decide_eq_false hh).trans (decide_eq_false hh').symm
  have exactC (a b : V) : C (E a) (E b)=c a b := by
    have iff : (∃ u v, E u=E a ∧ E v=E b ∧ c u v=true) ↔ c a b=true := by
      constructor
      · rintro ⟨u,v,hu,hv,h⟩
        rw [inj hu,inj hv] at h
        exact h
      · intro h
        exact ⟨a,b,rfl,rfl,h⟩
    cases cc : c a b
    · have hn := fun h => Bool.false_ne_true (cc.symm.trans (iff.mp h))
      exact decide_eq_false hn
    · have hp := iff.mpr cc
      exact decide_eq_true hp
  obtain ⟨f,h⟩ := fin7_spokes P ps pi pt C Cs
  refine ⟨fun a=>f (E a),fun a b e F=>h _ _ ⟨a,b,rfl,rfl,e⟩ ?_⟩
  rwa [exactC]

/-- Bikov's degree bound, directly on a finite symmetric irreflexive graph.
The two coloring hypotheses are precisely Ramsey and minimality at v. -/
theorem bikov_degree_eight {V : Type*}
    (adj : V→V→Prop)
    (sym : ∀ ⦃a b⦄, adj a b→adj b a) (irr : ∀ a,¬adj a a)
    (v : V) [Fintype {a : V // adj v a}]
    (noK4 : ∀ a b c, adj v a → adj v b → adj v c →
      adj a b → adj a c → adj b c → False)
    (ramsey : ∀ C : V→V→Bool, (∀ a b,C a b=C b a) → ¬ Safe adj C)
    (delete : ∃ c : V→V→Bool, (∀ a b,c a b=c b a) ∧
      Safe (fun a b => a≠v ∧ b≠v ∧ adj a b) c) :
    8 ≤ Fintype.card {a : V // adj v a} := by
  classical
  by_contra! lo
  obtain ⟨c,cs,old⟩ := delete
  let R (a b : {a : V // adj v a}) := adj a.val b.val
  obtain ⟨localF,safe⟩ := small_spokes (by omega : Fintype.card {a : V // adj v a}≤7)
    R (fun {_ _} h=>sym h) (fun a=>irr a.val)
    (fun a b c=>noK4 a b c a.property b.property c.property)
    (fun a b=>c a.val b.val) (fun a b=>cs a b)
  let f (a : V) := if h : adj v a then localF ⟨a,h⟩ else false
  have linked : ∀ a b, adj v a→adj v b→adj a b→¬(f a=c a b ∧ f b=c a b) := by
    intro a b aN bN ab
    simpa [f,aN,bN] using safe ⟨a,aN⟩ ⟨b,bN⟩ ab
  obtain ⟨C,S,ok,_⟩ := lift_link adj sym irr v c cs old f linked
  exact ramsey C S ok

#print axioms bikov_degree_eight
end BikovLocal
