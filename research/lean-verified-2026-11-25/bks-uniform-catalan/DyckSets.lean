import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.SetTheory.Cardinal.Finite

namespace FussCover
open DyckStep

def prefixCard {n : ℕ} (S : Finset (Fin n)) (q : ℕ) : ℕ :=
    (S.filter fun i => i.val<q).card

def BallotSet (j : ℕ) :=
    {S : Finset (Fin (2*j)) // S.card=j ∧ ∀ q : ℕ, prefixCard Sᶜ q ≤ prefixCard S q}

def steps {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : DyckStep := if i ∈ S then U else D

lemma count_ofFn {α : Type} [DecidableEq α] {n : ℕ} (a : α) (v : Fin n → α) :
    (List.ofFn v).count a = (Finset.univ.filter (fun i => v i=a)).card := by
  simpa only [List.Vector.get_ofFn,List.Vector.toList_ofFn] using
    (Fin.card_filter_univ_eq_vector_get_eq_count a (List.Vector.ofFn v)).symm

lemma count_prefix {n : ℕ} (v : Fin n → DyckStep) (s : DyckStep) (q : ℕ) :
    ((List.ofFn v).take q).count s =
    (Finset.univ.filter (fun i => i.val<q ∧ v i=s)).card := by
  let m := min q n
  have leN : m≤n := min_le_right _ _
  have H : (List.ofFn v).take q = (List.ofFn v).take m := by
    change (List.ofFn v).take q = (List.ofFn v).take (min q n)
    have e := List.take_take (l:=List.ofFn v) (i:=q) (j:=(List.ofFn v).length)
    simp at e ⊢
  rw [H,←Fin.ofFn_take_eq_take_ofFn leN,count_ofFn]
  apply Finset.card_bij (fun i _ => Fin.castLE leN i)
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have l := i.isLt
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_castLE]
    change v (Fin.castLE leN i)=s at hi'
    exact ⟨lt_of_lt_of_le l (min_le_left _ _),hi'⟩
  · intro a _ b _ he
    exact Fin.ext (congrArg (fun x : Fin n => x.val) he)
  · intro b hb
    have hb' := (Finset.mem_filter.mp hb).2
    let a : Fin m := ⟨b.val,by dsimp only [m]; exact lt_min hb'.1 b.isLt⟩
    have e : Fin.castLE leN a=b := Fin.ext rfl
    refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,e⟩
    change v (Fin.castLE leN a)=s
    rw [e,hb'.2]

lemma u_count {n : ℕ} (S : Finset (Fin n)) (q : ℕ) :
    ((List.ofFn (steps S)).take q).count U = prefixCard S q := by
  rw [count_prefix,prefixCard]
  congr 1; ext i
  by_cases h : i ∈ S <;> simp [steps,h]
lemma d_count {n : ℕ} (S : Finset (Fin n)) (q : ℕ) :
    ((List.ofFn (steps S)).take q).count D = prefixCard Sᶜ q := by
  rw [count_prefix,prefixCard]
  congr 1; ext i
  by_cases h : i ∈ S <;> simp [steps,h]

lemma prefix_full {n : ℕ} (S : Finset (Fin n)) : prefixCard S n=S.card := by
  unfold prefixCard
  rw [Finset.filter_true_of_mem (fun i _ => i.isLt)]

lemma comp_card {j : ℕ} (S : Finset (Fin (2*j))) (e : S.card=j) : (Sᶜ : Finset _).card=j := by
  rw [Finset.card_compl,e,Fintype.card_fin]; omega

def toDyck {j : ℕ} (S : BallotSet j) : {d : DyckWord // d.semilength=j} := by
  let T := S.val
  have c := S.property.1
  have B := S.property.2
  have u : (List.ofFn (steps T)).count U = j := by
    simpa only [prefix_full,List.take_of_length_le (show (List.ofFn (steps T)).length≤2*j by simp)]
      using (u_count T (2*j)).trans ((prefix_full T).trans c)
  have v : (List.ofFn (steps T)).count D = j := by
    simpa only [prefix_full,List.take_of_length_le (show (List.ofFn (steps T)).length≤2*j by simp)]
      using (d_count T (2*j)).trans ((prefix_full _).trans (comp_card T c))
  let d : DyckWord := ⟨List.ofFn (steps T),u.trans v.symm,fun q => by rw [u_count,d_count]; exact B q⟩
  exact ⟨d,u⟩

def fromDyck {j : ℕ} (d : {w : DyckWord // w.semilength=j}) : BallotSet j := by
  have len : d.1.toList.length=2*j := (DyckWord.two_mul_semilength_eq_length (p:=d.1)).symm.trans (congrArg (2*·) d.2)
  let v : Fin (2*j) → DyckStep := fun i => d.1.toList.get (Fin.cast len.symm i)
  have L : List.ofFn v=d.1.toList := by
    apply List.ext_get (by simp [len])
    intro i h1 h2
    simp [v]
  let S := Finset.univ.filter (fun i => v i=U)
  have eq : steps S=v := by
    ext i
    rcases DyckStep.dichotomy (v i) with e|e <;> simp [steps,S,e]
  refine ⟨S, ?_, ?_⟩
  · exact (count_ofFn U v).symm.trans ((congrArg (List.count U) L).trans d.2)
  · intro q
    rw [←u_count S,←d_count S,eq,L]
    exact d.1.count_D_le_count_U q

lemma toDyck_injective (j : ℕ) : Function.Injective (@toDyck j) := by
  intro A B E
  have e : List.ofFn (steps A.1)=List.ofFn (steps B.1) := congrArg (fun x => x.val.toList) E
  have e' := List.ofFn_injective e
  apply Subtype.ext
  ext i
  have a := congrFun e' i
  change (if i∈A.1 then U else D) = (if i∈B.1 then U else D) at a
  split_ifs at a <;> simp_all

lemma toDyck_surjective (j : ℕ) : Function.Surjective (@toDyck j) := by
  intro d
  use fromDyck d
  apply Subtype.ext
  apply DyckWord.ext
  change List.ofFn (steps (fromDyck d).val)=d.val.toList
  have len : d.1.toList.length=2*j := (DyckWord.two_mul_semilength_eq_length (p:=d.1)).symm.trans (congrArg (2*·) d.2)
  let v : Fin (2*j) → DyckStep := fun i => d.1.toList.get (Fin.cast len.symm i)
  have L : List.ofFn v=d.1.toList := by
    apply List.ext_get (by simp [len])
    intro i h1 h2
    simp [v]
  have E : steps (fromDyck d).val = v := by
    ext i
    change steps (Finset.univ.filter (fun k => v k=U)) i = v i
    rcases DyckStep.dichotomy (v i) with e|e <;> simp [steps,e]
  rwa [E]

theorem ballot_count (j : ℕ) : Nat.card (BallotSet j)=catalan j := by
  rw [Nat.card_congr (Equiv.ofBijective _ ⟨toDyck_injective j,toDyck_surjective j⟩)]
  rw [Nat.card_eq_fintype_card,DyckWord.card_dyckWord_semilength_eq_catalan]

end FussCover
