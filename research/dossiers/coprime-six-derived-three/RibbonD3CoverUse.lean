import RibbonD3CoverCore
import RibbonD3FieldCharts
import RibbonD3BucketData

namespace RibbonD3MateData
open RibbonD3Field (label raw)

def linked (k : RibbonD3Field.Count) : Prop :=
  let F := RibbonD3Field.chart k
  let M := charts[k.val]!
  F.key = (M.source,M.rotation) ∧ F.start = M.startSide ∧
    F.ports.map Fin.val = M.ports.toList
instance (k : RibbonD3Field.Count) : Decidable (linked k) := by unfold linked; infer_instance

theorem linked_all (k : RibbonD3Field.Count) : linked k := by fin_cases k <;> decide +kernel

def bucketIndexed (F : RibbonD3Field.Chart) (B : Array (List Nat)) : Bool :=
  (List.range 128).all fun i => F.map[i]! < B.size && (B[F.map[i]!]!).contains i

def bucketAll (C : Chart) (E : Array ExactRow) (B : Array (List Nat)) : Bool :=
  B.all fun l => l.all fun a => l.all fun b => !(a < b) || hasMate C E a b

theorem checkedBucket (k : RibbonD3Field.Count) :
    bucketIndexed (RibbonD3Field.chart k) buckets[k.val]! &&
      bucketAll charts[k.val]! exactRows[k.val]! buckets[k.val]! :=
  by fin_cases k <;> decide +kernel

theorem fast_cover (k : RibbonD3Field.Count) :
    checkCover (RibbonD3Field.chart k) charts[k.val]! exactRows[k.val]! = true := by
  have H := Bool.and_eq_true_iff.mp (checkedBucket k)
  unfold checkCover
  apply List.all_eq_true.mpr
  intro a hA
  apply List.all_eq_true.mpr
  intro b hB
  let f := (RibbonD3Field.chart k).map
  by_cases ab : a < b
  · by_cases same : f[a]! = f[b]!
    · have A := List.all_eq_true.mp H.1 a hA
      have B := List.all_eq_true.mp H.1 b hB
      change (decide (f[a]! < buckets[k.val]!.size) &&
        ((buckets[k.val]!)[ f[a]!]!).contains a) = true at A
      change (decide (f[b]! < buckets[k.val]!.size) &&
        ((buckets[k.val]!)[ f[b]!]!).contains b) = true at B
      have ha : f[a]! < buckets[k.val]!.size :=
        of_decide_eq_true ((Bool.and_eq_true_iff.mp A).1)
      have ha' := (Bool.and_eq_true_iff.mp A).2
      have hb' := (Bool.and_eq_true_iff.mp B).2
      rw [←same] at hb'
      have ga : a ∈ (buckets[k.val]!)[ f[a]!]! := by simpa using ha'
      have gb : b ∈ (buckets[k.val]!)[ f[a]!]! := by simpa using hb'
      have p := Array.all_eq_true.mp H.2 (f[a]!) ha
      have E : ((buckets[k.val]!)[ f[a]!]!).all (fun u =>
          ((buckets[k.val]!)[ f[a]!]!).all (fun v => !(u < v) || hasMate charts[k.val]! exactRows[k.val]! u v)) = true := by
        simp only [getElem!_pos (buckets[k.val]!) (f[a]!) ha]
        exact p
      have Q := List.all_eq_true.mp (List.all_eq_true.mp E a ga) b gb
      change (!(a < b && f[a]! == f[b]!) || hasMate charts[k.val]! exactRows[k.val]! a b) = true
      simpa [ab,same] using Q
    · change (!(a < b && f[a]! == f[b]!) || _) = true
      simp [ab,same]
  · simp [ab]

theorem rep_unique (k : RibbonD3Field.Count) : repsUnique (RibbonD3Field.chart k) := by
  intro i j e
  let A := (RibbonD3Field.chart k).reps
  have hi : i.val < A.toList.length := by simpa [A] using i.isLt
  have hj : j.val < A.toList.length := by simpa [A] using j.isLt
  have E : A.toList[i.val] = A.toList[j.val] := by simpa [A] using e
  exact Fin.ext ((List.Nodup.getElem_inj_iff (RibbonD3Field.charts_nodup k) (hi:=hi) (hj:=hj)).mp E)

theorem selected_cover (k : RibbonD3Field.Count) {a b : Fin 128} (ab : a.val < b.val)
    (e : label (raw (RibbonD3Field.chart k) a) = label (raw (RibbonD3Field.chart k) b)) :
    (64 ≤ b.val ∧ ∃ i : Fin charts[k.val]!.rows.size,
      charts[k.val]!.rows[i].i = a.val ∧ charts[k.val]!.rows[i].j = b.val) ∨
    ∃ i : Fin (exactRows[k.val]!).size,
      (exactRows[k.val]!)[i].i = a.val ∧ (exactRows[k.val]!)[i].j = b.val := by
  exact cover_sound (RibbonD3Field.charts_shape k) (rep_unique k) (fast_cover k) ab e

#print axioms linked_all
#print axioms selected_cover
end RibbonD3MateData
