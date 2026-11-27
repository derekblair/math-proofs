import KNeutralDecider
import Mathlib.Data.List.Pi
import Mathlib.Data.Finset.Sort

namespace KInventory

def enumPi {ι : Type*} [DecidableEq ι] {α : ι → Type*} (L : List ι)
    (h : ∀ i, i ∈ L) (F : ∀ i, List (α i)) : List (∀ i, α i) :=
  (L.pi F).map fun f i => f i (h i)

theorem mem_enumPi {ι : Type*} [DecidableEq ι] {α : ι → Type*} (L : List ι)
    (h : ∀ i, i ∈ L) (F : ∀ i, List (α i)) (cover : ∀ i (x : α i), x ∈ F i)
    (x : ∀ i, α i) : x ∈ enumPi L h F := by
  apply List.mem_map.mpr
  let g : ∀ i ∈ L, α i := fun i _ => x i
  exact ⟨g,(List.mem_pi F g).mpr (fun i _ => cover i (x i)),rfl⟩

def finList (n : ℕ) : List (Fin n) := List.finRange n
theorem mem_finList {n : ℕ} (i : Fin n) : i ∈ finList n := by simp [finList]

def finPi {n : ℕ} {α : Fin n → Type*} (F : ∀ i, List (α i)) : List (∀ i, α i) :=
  enumPi (finList n) mem_finList F

theorem mem_finPi {n : ℕ} {α : Fin n → Type*} (F : ∀ i, List (α i))
    (cover : ∀ i (x : α i), x ∈ F i) (x : ∀ i, α i) : x ∈ finPi F :=
  mem_enumPi _ _ _ cover x

def enumSub {α : Type*} (L : List α) (P : α → Prop) [DecidablePred P] : List (Subtype P) :=
  (L.filter fun x => decide (P x)).attach.map
    fun z => ⟨z.val,by
      have hz : z.val ∈ L.filter (fun x => decide (P x)) := z.property
      simp only [List.mem_filter,decide_eq_true_eq] at hz
      exact hz.2⟩

theorem mem_enumSub {α : Type*} (L : List α) (P : α → Prop) [DecidablePred P]
    (h : ∀ x, P x → x ∈ L) (z : Subtype P) : z ∈ enumSub L P := by
  have hz : z.val ∈ L.filter (fun x => decide (P x)) :=
    List.mem_filter.mpr ⟨h z.val z.property,decide_eq_true z.property⟩
  unfold enumSub
  apply List.mem_map.mpr
  exact ⟨⟨z.val,hz⟩,by simp,Subtype.ext rfl⟩

def enumZ (D : Finset ℤ) : List {x : ℤ // x ∈ D} :=
  enumSub (D.sort) (· ∈ D)

theorem mem_enumZ (D : Finset ℤ) (x : {x : ℤ // x ∈ D}) : x ∈ enumZ D :=
  mem_enumSub _ _ (fun _ h => by simpa using h) x

def bitList : List Bool := [false,true]
theorem mem_bitList (q : Bool) : q ∈ bitList := by cases q <;> simp [bitList]

end KInventory

#print axioms KInventory.mem_finPi
#print axioms KInventory.mem_enumZ
