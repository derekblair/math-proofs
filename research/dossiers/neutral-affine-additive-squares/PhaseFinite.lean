import PhaseProduct

namespace PhaseFinite

open PhaseProduct WeightedWalk EdgeExpansion
variable {Q E : Type*} (M : Machine Q E) (B : ℤ)

abbrev Coord (B : ℤ) := {z : ℤ // z ∈ IntegerTrace.box B}
abbrev State (Q : Type*) (B : ℤ) := Q × Coord B × Bool
abbrev Arc (M : Machine Q E) (B : ℤ) :=
  {u : E × Coord B × Bool // M.mult*(u.2.1.val)+M.ex u.1 ∈ IntegerTrace.box B}

instance : Fintype (Coord B) := (IntegerTrace.box B).fintypeCoeSort

def Snode (p : State Q B) : Node Q := ⟨p.1,p.2.1.val,p.2.2⟩

def pack (p : Node Q) (h : p.ex ∈ IntegerTrace.box B) : State Q B :=
  ⟨p.loc,⟨p.ex,h⟩,p.phase⟩

def src (u : Arc M B) : State Q B :=
  ⟨M.src u.val.1,u.val.2⟩

def dst (u : Arc M B) : State Q B :=
  ⟨M.dst u.val.1,⟨M.mult*u.val.2.1.val+M.ex u.val.1,u.property⟩,phase M u.val.2.2⟩

def label (u : Arc M B) := cost M u.val.1 u.val.2.2

abbrev Rel := EdgeExpansion.edge (src M B) (dst M B) (label M B)

theorem aug_append (p : Node Q) (U V : List E) :
    aug M p (U++V) = aug M (aug M p U) V := by
  induction U generalizing p with
  | nil => rfl
  | cons e U ih => exact ih _

theorem from_walk {x y : State Q B} {C : List ℤ} (h : Walk (Rel M B) x y C) :
    ∃ L, Path M x.1 y.1 L ∧ aug M (Snode B x) L = Snode B y ∧
      costs M x.2.2 L = C := by
  induction h with
  | nil x => exact ⟨[],.nil _,rfl,rfl⟩
  | @step x y z e C a t ih =>
    obtain ⟨u, rfl, rfl, rfl⟩ := a
    obtain ⟨L,hL,ha,hc⟩ := ih
    exact ⟨u.val.1::L,.cons _ hL,ha,by exact congrArg (label M B u :: ·) hc⟩

theorem to_walk {x y : Q} {L : List E} (h : Path M x y L)
    (v : ℤ) (q : Bool)
    (hh : ∀ U V : List E, L=U++V → (aug M ⟨x,v,q⟩ U).ex ∈ IntegerTrace.box B) :
    ∃ (h₁ : v ∈ IntegerTrace.box B)
      (h₂ : (aug M ⟨x,v,q⟩ L).ex ∈ IntegerTrace.box B),
      Walk (Rel M B) (pack B ⟨x,v,q⟩ h₁) (pack B (aug M ⟨x,v,q⟩ L) h₂) (costs M q L) := by
  induction h generalizing v q with
  | nil x =>
    have hv := hh [] [] rfl
    exact ⟨hv,hv,.nil _⟩
  | @cons e y L h ih =>
    have hv := hh [] (e::L) rfl
    have ht : ∀ U V : List E, L = U ++ V →
        (aug M (next M e ⟨M.src e,v,q⟩) U).ex ∈ IntegerTrace.box B := by
      intro U V h
      exact hh (e::U) V (congrArg (e::·) h)
    obtain ⟨h₁,h₂,w⟩ := ih (M.mult*v+M.ex e) (phase M q) ht
    let u : Arc M B := ⟨⟨e,⟨v,hv⟩,q⟩,h₁⟩
    refine ⟨hv,h₂,.step (show Rel M B _ _ _ from ⟨u,rfl,rfl,rfl⟩) w⟩

variable [Fintype Q] [Fintype E] [DecidableEq Q] [DecidableEq E]

def accept (x y : Q) (hb : 0 ∈ IntegerTrace.box B) : Bool :=
  FiniteEdges.test (src M B) (dst M B) (label M B)
    ⟨x,⟨0,hb⟩,false⟩ ⟨y,⟨0,hb⟩,false⟩ ||
  FiniteEdges.test (src M B) (dst M B) (label M B)
    ⟨x,⟨0,hb⟩,false⟩ ⟨y,⟨0,hb⟩,true⟩

theorem accept_iff (x y : Q) (hb : 0 ∈ IntegerTrace.box B) (C : ℤ)
    (hE : ∀ e, |M.ex e| ≤ C) (ha : 1 < |M.mult|)
    (hB : 0 ≤ B) (hc : C ≤ (|M.mult|-1)*B) :
    accept M B x y hb = true ↔
    ∃ L, Path M x y L ∧ ScalarTrace.zeval M.mult 0 (L.map M.ex) = 0 ∧
      ScalarTrace.zeval (s M) 0 (L.map M.nu) = 0 := by
  unfold accept
  rw [Bool.or_eq_true,FiniteEdges.test_iff,FiniteEdges.test_iff]
  constructor
  · intro hh
    have aux (q : Bool) (W : List ℤ)
        (h : Walk (Rel M B) ⟨x,⟨0,hb⟩,false⟩ ⟨y,⟨0,hb⟩,q⟩ W) (hz : W.sum=0) :
        ∃ L, Path M x y L ∧ ScalarTrace.zeval M.mult 0 (L.map M.ex)=0 ∧
          ScalarTrace.zeval (s M) 0 (L.map M.nu)=0 := by
      obtain ⟨L,hL,hN,hW⟩ := from_walk M B h
      have he := congrArg Node.ex hN
      rw [aug_ex] at he
      refine ⟨L,hL,he,(zero_iff M ⟨x,0,false⟩ L).mpr ?_⟩
      rw [show costs M false L = W from hW,hz]
    rcases hh with ⟨W,h,z⟩ | ⟨W,h,z⟩
    · exact aux false W h z
    · exact aux true W h z
  · rintro ⟨L,hL,he,hn⟩
    let p : Node Q := ⟨x,0,false⟩
    have all (U V : List E) (h : L=U++V) : (aug M p U).ex ∈ IntegerTrace.box B := by
      rw [aug_ex]
      change ScalarTrace.zeval M.mult 0 (U.map M.ex) ∈ IntegerTrace.box B
      apply IntegerTrace.can_clip M.mult B C ha hB hc _ (V.map M.ex)
      · intro e he
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
        exact hE i
      · simpa only [h,List.map_append] using he
    obtain ⟨h1,h2,w⟩ := to_walk M B hL 0 false all
    have hv : (aug M p L).ex=0 := (aug_ex M p L).trans he
    have hl : (aug M p L).loc=y := aug_loc M hL 0 false
    have hz := (zero_iff M p L).mp hn
    let q := (aug M p L).phase
    have hw : pack B (aug M p L) h2 = (⟨y,⟨0,hb⟩,q⟩ : State Q B) := by
      apply Prod.ext
      · exact hl
      · apply Prod.ext
        · exact Subtype.ext hv
        · rfl
    change Walk (Rel M B) ⟨x,⟨0,hb⟩,false⟩ (pack B (aug M p L) h2) _ at w
    rw [hw] at w
    cases hq : q with
    | false => exact Or.inl ⟨_,by simpa only [hq] using w,hz⟩
    | true => exact Or.inr ⟨_,by simpa only [hq] using w,hz⟩

end PhaseFinite

#print axioms PhaseFinite.accept_iff
