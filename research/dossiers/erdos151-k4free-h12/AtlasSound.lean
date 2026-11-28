import AtlasNumeric
import LinkSound
import MarkedLinkTable
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Nodup

namespace BikovEight

def R (m : Nat) (i j : Fin 8) : Prop := hasEdge m i.val j.val=true

lemma has_sym (m i j : Nat) : hasEdge m i j=hasEdge m j i := by
  by_cases e : i=j
  · subst j
    rfl
  · simp [hasEdge,e,Ne.symm e,edgeID,min_comm,max_comm]

lemma ordered_iff (i j : Nat) : (i,j)∈orderedEdges ↔ i<j ∧ j<8 := by
  unfold orderedEdges
  simp only [List.mem_flatMap,List.mem_range,List.mem_map]
  constructor
  · rintro ⟨b,hb,a,ha,e⟩
    cases e
    exact ⟨ha,hb⟩
  · rintro ⟨ij,j8⟩
    exact ⟨j,j8,i,ij,rfl⟩

theorem cut_sound (m s : Nat) (h : cutCheck m s=true)
    (c : Fin 8→Fin 8→Bool) (cs : ∀ a b,c a b=c b a) :
    ∃ f : Fin 8→Bool, ∀ i j,R m i j→¬ (f i=c i j ∧ f j=c i j) := by
  let E := orderedEdges.filter (fun p=>hasEdge m p.1 p.2)
  let lab (p : Nat×Nat) := c (Fin.ofNat 8 p.1) (Fin.ofNat 8 p.2)
  have same : BikovLocal.defect E s =
      orderedEdges.filter (fun e=>hasEdge m e.1 e.2 && (s.testBit e.1 == s.testBit e.2)) := by
    unfold BikovLocal.defect E
    simp [List.filter_filter,Bool.and_comm]
  have bound : (BikovLocal.defect E s).length≤1 := by
    rw [same]
    exact of_decide_eq_true h
  obtain ⟨f,p⟩ := BikovLocal.of_defect E E (fun _ h=>h) s bound lab
  have ord (i j : Fin 8) (ij : i<j) (e : R m i j) :
      ¬ (f i.val=c i j ∧ f j.val=c i j) := by
    have elig : (i.val,j.val)∈E := List.mem_filter.mpr
      ⟨(ordered_iff ..).mpr ⟨ij,j.isLt⟩,e⟩
    have H (v : Fin 8) : (Fin.ofNat 8 v.val)=v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
    simpa [lab,H] using p _ elig
  refine ⟨fun i=>f i.val,?_⟩
  intro i j e h
  rcases lt_trichotomy i j with l|eq|r
  · exact ord i j l e h
  · subst j
    simp [R,hasEdge] at e
  · have rr : R m j i := by simpa [R,has_sym m j.val i.val] using e
    exact ord j i r rr ⟨h.2.trans (cs i j),h.1.trans (cs i j)⟩

theorem packed_names : ∀ (i : Fin 7) (a b : Fin 8),
    hasEdge names[i.val]! a.val b.val=Erdos151MarkedLinkTable.adj i a b := by
  decide +kernel

theorem iso_sound (i : Fin 7) (m p : Nat) (h : isoCheck names[i.val]! m p=true) :
    ∃ σ : Equiv.Perm (Fin 8), ∀ a b, R m (σ a) (σ b) ↔ Erdos151MarkedLinkTable.adj i a b=true := by
  classical
  have hb (j : Nat) : permAt p j<8 := by
    have H : 7 &&& (p >>> (3*j)) ≤ 7 := Nat.and_le_left
    unfold permAt
    rw [Nat.and_comm]
    omega
  let f (j : Fin 8) : Fin 8 := ⟨permAt p j.val,hb j.val⟩
  have H : (((List.range 8).map (permAt p)).Nodup) ∧
      orderedEdges.all (fun e => hasEdge names[i.val]! e.1 e.2 ==
        hasEdge m (permAt p e.1) (permAt p e.2))=true := by simpa [isoCheck] using h
  have inj : Function.Injective f := by
    intro a b e
    apply Fin.ext
    have ee := congrArg Fin.val e
    change permAt p a.val=permAt p b.val at ee
    have ha : a.val<8 := a.isLt
    have hb : b.val<8 := b.isLt
    exact ( (List.nodup_map_iff_inj_on List.nodup_range).mp H.1) a.val (List.mem_range.mpr ha) b.val (List.mem_range.mpr hb) ee
  have bij : Function.Bijective f := ⟨inj,Finite.surjective_of_injective inj⟩
  let σ := Equiv.ofBijective f bij
  have ord (a b : Fin 8) (l : a<b) :
      hasEdge m (σ a).val (σ b).val=Erdos151MarkedLinkTable.adj i a b := by
    have mem := (ordered_iff a.val b.val).mpr ⟨l,b.isLt⟩
    have q := List.all_eq_true.mp H.2 _ mem
    have q' := beq_iff_eq.mp q
    change hasEdge m (permAt p a.val) (permAt p b.val)=_
    rw [←q',packed_names]
  refine ⟨σ,fun a b=>?_⟩
  change hasEdge m (σ a).val (σ b).val=true ↔ _
  rcases lt_trichotomy a b with l|eq|r
  · rw [ord a b l]
  · subst b
    rw [←packed_names]
    simp [hasEdge]
  · rw [has_sym m (σ a).val (σ b).val,ord b a r,←packed_names,←packed_names]
    rw [has_sym]

theorem check_sound (m v : Nat) (h : check m v=true) :
    (∀ c : Fin 8→Fin 8→Bool, (∀ a b,c a b=c b a) →
       ∃ f : Fin 8→Bool, ∀ i j,R m i j → ¬(f i=c i j ∧ f j=c i j)) ∨
    (∃ i : Fin 7, ∃ σ : Equiv.Perm (Fin 8), ∀ a b,
      R m (σ a) (σ b) ↔ Erdos151MarkedLinkTable.adj i a b=true) := by
  by_cases hv : v<256
  · exact Or.inl (fun c cs=>cut_sound m v (by simpa [check,hv] using h) c cs)
  · have H : (((v-256)&&&7)<7) ∧
      isoCheck (names[((v-256)&&&7)]!) m ((v-256)>>>3)=true := by
      simpa [check,hv] using h
    exact Or.inr ⟨⟨_,H.1⟩,iso_sound ⟨_,H.1⟩ m _ H.2⟩

#print axioms check_sound
end BikovEight
