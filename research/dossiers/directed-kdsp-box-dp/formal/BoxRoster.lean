import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Disjoint
import Mathlib.Tactic.Tauto

namespace BoxRoster
set_option linter.unusedSectionVars false

variable {V A : Type*} [DecidableEq V] [DecidableEq A]

/-- Arc identifiers may contain direction, commodity, and parallel-edge ID.
No quotient identifying arcs with equal endpoints is used. -/
noncomputable def touch (tail head : A → V) (S : Finset V) (F : Finset A) : Finset A :=
  F.filter (fun a => tail a ∈ S ∨ head a ∈ S)

noncomputable def roster (tail head : A → V) (x : V) (F : Finset A) : Finset A :=
  touch tail head {x} F

noncomputable def boundary (tail head : A → V) (S : Finset V) (F : Finset A) : Finset A :=
  F.filter (fun a => (tail a ∈ S ∧ head a ∉ S) ∨ (head a ∈ S ∧ tail a ∉ S))

/-- Strip the arcs that are internal to the parent; child boundary arcs
which survive are exactly the parent's exterior arcs at that child. -/
noncomputable def away (tail head : A → V) (S : Finset V) (B : Finset A) : Finset A :=
  B.filter (fun a => tail a ∉ S ∧ head a ∉ S)

def confined (tail head : A → V) (S : Finset V) (F : Finset A) : Prop :=
  touch tail head S F = F

def agree (tail head : A → V) (L R : Finset V) (FL FR : Finset A) : Prop :=
  touch tail head L FR ⊆ FL ∧ touch tail head R FL ⊆ FR

def realizes (tail head : A → V) (S : Finset V) (B : Finset A)
    (accept : V → Finset A → Prop) (F : Finset A) : Prop :=
  confined tail head S F ∧ boundary tail head S F = B ∧
    ∀ x ∈ S, accept x (roster tail head x F)

@[simp] theorem mem_touch (tail head : A → V) (S : Finset V) (F : Finset A) (a : A) :
    a ∈ touch tail head S F ↔ a ∈ F ∧ (tail a ∈ S ∨ head a ∈ S) := by
  simp [touch]

@[simp] theorem mem_roster (tail head : A → V) (x : V) (F : Finset A) (a : A) :
    a ∈ roster tail head x F ↔ a ∈ F ∧ (tail a = x ∨ head a = x) := by
  simp [roster]

@[simp] theorem mem_boundary (tail head : A → V) (S : Finset V) (F : Finset A) (a : A) :
    a ∈ boundary tail head S F ↔ a ∈ F ∧
      ((tail a ∈ S ∧ head a ∉ S) ∨ (head a ∈ S ∧ tail a ∉ S)) := by
  simp [boundary]

@[simp] theorem mem_away (tail head : A → V) (S : Finset V) (B : Finset A) (a : A) :
    a ∈ away tail head S B ↔ a ∈ B ∧ tail a ∉ S ∧ head a ∉ S := by
  simp [away]

theorem confined_iff (tail head : A → V) (S : Finset V) (F : Finset A) :
    confined tail head S F ↔ ∀ a ∈ F, tail a ∈ S ∨ head a ∈ S := by
  unfold confined
  constructor
  · intro h a ha
    exact ((mem_touch _ _ _ _ _).mp (h.symm ▸ ha)).2
  · intro h
    ext a
    simp only [mem_touch]
    exact ⟨And.left, fun ha => ⟨ha,h a ha⟩⟩

theorem roster_restrict (tail head : A → V) {S : Finset V} {x : V} (hx : x ∈ S)
    (F : Finset A) :
    roster tail head x (touch tail head S F) = roster tail head x F := by
  ext a
  simp only [mem_roster, mem_touch]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨ha, ht|hh⟩
    · exact ⟨⟨ha,Or.inl (ht.symm ▸ hx)⟩,Or.inl ht⟩
    · exact ⟨⟨ha,Or.inr (hh.symm ▸ hx)⟩,Or.inr hh⟩

theorem touch_glue (tail head : A → V) (L R : Finset V) (FL FR : Finset A)
    (hL : confined tail head L FL) (hR : confined tail head R FR)
    (h : agree tail head L R FL FR) :
    touch tail head L (FL ∪ FR) = FL ∧ touch tail head R (FL ∪ FR) = FR := by
  have hL := (confined_iff tail head L FL).mp hL
  have hR := (confined_iff tail head R FR).mp hR
  constructor
  · ext a
    simp only [mem_touch, Finset.mem_union]
    exact ⟨fun ha => ha.1.elim id (fun hf => h.1 (by simp [hf,ha.2])),
      fun ha => ⟨Or.inl ha,hL a ha⟩⟩
  · ext a
    simp only [mem_touch, Finset.mem_union]
    exact ⟨fun ha => ha.1.elim (fun hf => h.2 (by simp [hf,ha.2])) id,
      fun ha => ⟨Or.inr ha,hR a ha⟩⟩

theorem boundary_decomp (tail head : A → V) (L R : Finset V) (F : Finset A)
    (h : Disjoint L R) :
    boundary tail head (L ∪ R) F =
      away tail head R (boundary tail head L (touch tail head L F)) ∪
      away tail head L (boundary tail head R (touch tail head R F)) := by
  ext a
  have ht := fun (hl : tail a ∈ L) (hr : tail a ∈ R) => Finset.disjoint_left.mp h hl hr
  have hh := fun (hl : head a ∈ L) (hr : head a ∈ R) => Finset.disjoint_left.mp h hl hr
  simp only [mem_boundary, mem_away, mem_touch, Finset.mem_union]
  tauto

/-- Cross-child agreement can be tested from the boundary states alone. -/
theorem agree_from_boundary (tail head : A → V) (L R : Finset V) (FL FR : Finset A)
    (h : Disjoint L R) (hL : confined tail head L FL) (hR : confined tail head R FR) :
    agree tail head L R FL FR ↔
    touch tail head R (boundary tail head L FL) =
      touch tail head L (boundary tail head R FR) := by
  have hL := (confined_iff tail head L FL).mp hL
  have hR := (confined_iff tail head R FR).mp hR
  have hb (S T : Finset V) (F : Finset A)
      (hd : Disjoint S T) (hc : ∀ a ∈ F, tail a ∈ S ∨ head a ∈ S) :
      touch tail head T (boundary tail head S F) = touch tail head T F := by
    ext a
    have ht := fun (hs : tail a ∈ S) (ht : tail a ∈ T) => Finset.disjoint_left.mp hd hs ht
    have hh := fun (hs : head a ∈ S) (ht : head a ∈ T) => Finset.disjoint_left.mp hd hs ht
    simp only [mem_touch, mem_boundary]
    have hc' := hc a
    tauto
  rw [hb _ _ _ h hL, hb _ _ _ h.symm hR]
  constructor
  · intro ha
    ext a
    simp only [mem_touch]
    have hl := hL a
    have hr := hR a
    have hz₁ : a ∈ FR ∧ (tail a ∈ L ∨ head a ∈ L) → a ∈ FL := by
      intro hs
      exact ha.1 ((mem_touch _ _ _ _ _).mpr hs)
    have hz₂ : a ∈ FL ∧ (tail a ∈ R ∨ head a ∈ R) → a ∈ FR := by
      intro hs
      exact ha.2 ((mem_touch _ _ _ _ _).mpr hs)
    tauto
  · intro he
    exact ⟨fun _ ha => ((mem_touch _ _ _ _ _).mp (he.symm ▸ ha)).1,
      fun _ ha => ((mem_touch _ _ _ _ _).mp (he ▸ ha)).1⟩

/-- Constructive splitting/gluing theorem. Compatibility references only
the stored interfaces, not either child's internal arc choices. -/
theorem split_iff (tail head : A → V) (L R : Finset V) (B : Finset A)
    (accept : V → Finset A → Prop) (hd : Disjoint L R) :
    (∃ F, realizes tail head (L ∪ R) B accept F) ↔
      ∃ BL BR FL FR, realizes tail head L BL accept FL ∧
        realizes tail head R BR accept FR ∧
        touch tail head R BL = touch tail head L BR ∧
        B = away tail head R BL ∪ away tail head L BR := by
  constructor
  · rintro ⟨F,_,hB,hacc⟩
    let FL := touch tail head L F
    let FR := touch tail head R F
    have hL : confined tail head L FL := by
      apply (confined_iff tail head L FL).mpr
      exact fun a ha => ((mem_touch _ _ _ _ _).mp ha).2
    have hR : confined tail head R FR := by
      apply (confined_iff tail head R FR).mpr
      exact fun a ha => ((mem_touch _ _ _ _ _).mp ha).2
    have hag : agree tail head L R FL FR := by
      constructor <;> intro a ha <;> simp only [FL,FR,mem_touch] at ha ⊢ <;> tauto
    refine ⟨boundary tail head L FL,boundary tail head R FR,FL,FR,
      ⟨hL,rfl,?_⟩,⟨hR,rfl,?_⟩,(agree_from_boundary tail head L R FL FR hd hL hR).mp hag,?_⟩
    · intro x hx
      simpa only [FL,roster_restrict tail head hx] using hacc x (Finset.mem_union_left _ hx)
    · intro x hx
      simpa only [FR,roster_restrict tail head hx] using hacc x (Finset.mem_union_right _ hx)
    · exact hB.symm.trans (boundary_decomp tail head L R F hd)
  · rintro ⟨BL,BR,FL,FR,⟨hL,rfl,gL⟩,⟨hR,rfl,gR⟩,hmatch,rfl⟩
    have hag := (agree_from_boundary tail head L R FL FR hd hL hR).mpr hmatch
    obtain ⟨fL,fR⟩ := touch_glue tail head L R FL FR hL hR hag
    refine ⟨FL ∪ FR, ?_, ?_, ?_⟩
    · apply (confined_iff tail head _ _).mpr
      intro a ha
      rcases Finset.mem_union.mp ha with hl|hr
      · rcases (confined_iff tail head L FL).mp hL a hl with h|h
        · exact Or.inl (Finset.mem_union_left _ h)
        · exact Or.inr (Finset.mem_union_left _ h)
      · rcases (confined_iff tail head R FR).mp hR a hr with h|h
        · exact Or.inl (Finset.mem_union_right _ h)
        · exact Or.inr (Finset.mem_union_right _ h)
    · rw [boundary_decomp tail head L R (FL ∪ FR) hd,fL,fR]
    · intro x hx
      rcases Finset.mem_union.mp hx with hl|hr
      · rw [← roster_restrict tail head hl, fL]
        exact gL x hl
      · rw [← roster_restrict tail head hr, fR]
        exact gR x hr

#print axioms split_iff
end BoxRoster
