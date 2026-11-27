import Fiber
namespace IU.Slack
open Finset
open scoped BigOperators

abbrev Q := Nat × Bag × Nat

def parts (A : Bag) (t s : Nat) : Q := (pr A t,band A t s,(tail A t s).card)
def full (x : Q) : Nat := x.1+x.2.1.card+x.2.2
def Qfiber (t u s : Nat) (x : Q) := fiber (t+u+s) t s x.1 x.2.2 x.2.1

theorem full_parts (A : Bag) (t s : Nat) : full (parts A t s)=A.card := by
  have b : Disjoint (below A t) (band A t s) := disjoint_left.mpr (by
    intro x a c
    have xa := (mem_filter.mp a).2
    have xc := (mem_filter.mp c).2.1
    omega)
  have w : Disjoint (below A t ∪ band A t s) (tail A t s) := disjoint_left.mpr (by
    intro x a c
    have xc := (mem_filter.mp c).2
    rcases mem_union.mp a with ax|ax
    · have h := (mem_filter.mp ax).2
      omega
    · have h := (mem_filter.mp ax).2.2
      omega)
  change #(below A t)+ #(band A t s)+ #(tail A t s)=A.card
  rw [←card_union_of_disjoint b,←card_union_of_disjoint w,split_parts]

def Admissible (t u s : Nat) (x : Q) : Prop :=
   x.2.1 ⊆ mid t s ∧ x.1≤t ∧ x.2.2≤u ∧ t≤full x ∧ full x≤t+s

def Qcompat (t s : Nat) (x y : Q) : Prop :=
  ∃ i≤s, ((full x-t)+(full y-t)-s)+(t-x.1)+(t-y.1)+i ≤
    (x.2.1.filter (· < t+i)).card+(y.2.1.filter (· < t+i)).card

theorem compat_parts (A B : Bag) (t s : Nat) :
    Qcompat t s (parts A t s) (parts B t s) ↔ Compatible A B t s := by
  constructor <;> rintro ⟨i,hi,e⟩ <;> refine ⟨i,hi,?_⟩
  · rw [band_nested A hi,band_nested B hi]
    simp only [full_parts] at e
    simpa only [parts] using e
  · rw [band_nested A hi,band_nested B hi] at e
    simp only [full_parts]
    simpa only [parts] using e

def Good (I : Finset Q) (t u s : Nat) : Prop :=
  (∀ x∈I, Admissible t u s x) ∧ ∀ x∈I, ∀ y∈I, Qcompat t s x y

theorem Qfiber_mem {A : Bag} {x : Q} {t u s : Nat} (h : Admissible t u s x) :
    A∈Qfiber t u s x ↔ A⊆range (t+u+s) ∧ parts A t s=x := by
  rcases x with ⟨a,M,z⟩
  rw [Qfiber,fiber_mem h.1 (by omega)]
  simp [parts,and_assoc]

def lift (I : Finset Q) (t u s : Nat) : Sys := I.biUnion (Qfiber t u s)
def Qscore (w : Nat → Nat) (I : Finset Q) (t u : Nat) : Nat :=
  ∑ x∈I, (t.choose x.1)*(u.choose x.2.2)*w (full x)

theorem lift_valid {I : Finset Q} {t u s : Nat} (h : Good I t u s) :
    IsIU (lift I t u s) (t+u+s) t u := by
  refine ⟨?_,?_⟩
  · intro A a
    obtain ⟨x,xI,hx⟩ := mem_biUnion.mp a
    exact ((Qfiber_mem (h.1 x xI)).mp hx).1
  · intro A a B b
    obtain ⟨x,xI,hx⟩ := mem_biUnion.mp a
    obtain ⟨y,yI,hy⟩ := mem_biUnion.mp b
    have ax := ((Qfiber_mem (h.1 x xI)).mp hx).2
    have by' := ((Qfiber_mem (h.1 y yI)).mp hy).2
    have cx := h.2 x xI y yI
    rw [←ax,←by'] at cx
    have tA : t≤A.card := by rw [←full_parts A t s,ax]; exact (h.1 x xI).2.2.2.1
    have tB : t≤B.card := by rw [←full_parts B t s,by']; exact (h.1 y yI).2.2.2.1
    have ans := compatible_sound tA tB ((compat_parts A B t s).mp cx)
    exact ⟨ans.1,by omega⟩

theorem lift_score (w : Nat → Nat) {I : Finset Q} {t u s : Nat} (h : Good I t u s) :
    objective w (lift I t u s)=Qscore w I t u := by
  classical
  have pd : (↑I : Set Q).PairwiseDisjoint (Qfiber t u s) := by
    intro x xI y yI ne
    exact disjoint_left.mpr (by
      intro A ax ay
      exact ne (((Qfiber_mem (h.1 x xI)).mp ax).2.symm.trans
        ((Qfiber_mem (h.1 y yI)).mp ay).2))
  unfold objective lift Qscore
  rw [sum_biUnion pd]
  apply sum_congr rfl
  intro x xI
  have m : ∀ A∈Qfiber t u s x, A.card=full x := by
    intro A a
    exact (full_parts A t s).symm.trans (congrArg full ((Qfiber_mem (h.1 x xI)).mp a).2)
  calc
    _ = ∑ A∈Qfiber t u s x, w (full x) :=
      sum_congr rfl (fun A a => congrArg w (m A a))
    _ = _ := by
      rw [sum_const,Nat.nsmul_eq_mul,Qfiber,fiber_card (h.1 x xI).1 (by omega),show t+u+s-(t+s)=u by omega]

theorem original_to_graph (w : Nat → Nat) (F : Sys) {t u s : Nat}
    (hp : 0<t) (ok : IsIU F (t+u+s) t u) :
    ∃ I : Finset Q, Good I t u s ∧ objective w F≤Qscore w I t u := by
  classical
  obtain ⟨H,wH,vH,sH⟩ := stabilize_objective w F ok
  let I := H.image (fun A => parts A t s)
  have g : Good I t u s := by
    constructor
    · intro x xI
      obtain ⟨A,a,rfl⟩ := mem_image.mp xI
      have a1 : band A t s ⊆ mid t s := by
        intro k hk
        obtain ⟨_,l,r⟩ := mem_filter.mp hk
        exact mem_sdiff.mpr ⟨mem_range.mpr r,fun q => (Nat.not_lt_of_ge l) (mem_range.mp q)⟩
      have a2 : (tail A t s).card≤u := by
        have sub : tail A t s⊆last (t+u+s) t s := by
          intro k hk
          obtain ⟨ka,ki⟩ := mem_filter.mp hk
          exact mem_sdiff.mpr ⟨vH.1 A a ka,fun q => (Nat.not_lt_of_ge ki) (mem_range.mp q)⟩
        have c := card_le_card sub
        rw [card_sdiff_of_subset (range_mono (by omega)),card_range,card_range] at c
        omega
      obtain ⟨a3,a4⟩ := vH.2 A a A a
      have a3' : t≤A.card := by simpa using a3
      have a4' : A.card≤t+s := by simpa [show t+u+s-u=t+s by omega] using a4
      exact ⟨a1,prefix_le_index A t,a2,
        (full_parts A t s).symm ▸ a3',(full_parts A t s).symm ▸ a4'⟩
    · intro x xi y yi
      obtain ⟨A,a,ha⟩ := mem_image.mp xi
      obtain ⟨B,b,hb⟩ := mem_image.mp yi
      rw [←ha,←hb,compat_parts]
      have tA : t≤A.card := by simpa using (vH.2 A a A a).1
      have tB : t≤B.card := by simpa using (vH.2 B b B b).1
      exact (compatible_iff_witness tA tB).mpr (shifted_witness_band hp vH sH a b)
  refine ⟨I,g,?_⟩
  rw [←wH,←lift_score w g]
  apply sum_le_sum_of_subset
  intro A a
  have m : parts A t s∈I := mem_image.mpr ⟨A,a,rfl⟩
  exact mem_biUnion.mpr ⟨_,m,(Qfiber_mem (g.1 _ m)).mpr ⟨vH.1 A a,rfl⟩⟩

#print axioms original_to_graph
#print axioms lift_valid
#print axioms lift_score
end IU.Slack
