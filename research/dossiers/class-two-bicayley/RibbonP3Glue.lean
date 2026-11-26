import RibbonP3Transport
import RibbonP3Endpoint

namespace RibbonP3
open Ribbon5Bridge HaarUniversal36
variable {G : Type*} [Group G]

def vertAt (x y : G) (t : Fin 3) (i : Fin 64) := run x y (start G) (wordAt t i)
def word32 (t : Fin 3) := (wa t).toArray
def word64 (t : Fin 3) := (wa t ++ reverseWord (wb t)).toArray
def reflIdx (i : Fin 64) : Fin 64 :=
  if h : 32 < i.val then ⟨96-i.val,by have := i.isLt; omega⟩ else i

theorem refl_inj : Function.Injective reflIdx := by
  intro i j e
  apply Fin.ext
  have h := congrArg Fin.val e
  unfold reflIdx at h
  split at h <;> split at h <;> simp_all <;> omega

theorem stop_word (t : Fin 3) (x y : G) (nil : L G 5=⊥) :
    run x y (start G) (wa t) = (false,trace x y false a) ∧
    run x y (start G) (wb t) = (false,trace x y false a) := by
  obtain ⟨hb,ha',hb'⟩ := endpoint_all nil x y
  fin_cases t <;> rw [run_eq_trace,run_eq_trace] <;>
    simp [wa,wb,start,ha',hb',hb] <;> decide +kernel

theorem word32_size (t : Fin 3) : (word32 t).size=32 := by fin_cases t <;> decide
theorem word64_size (t : Fin 3) : (word64 t).size=64 := by fin_cases t <;> decide

theorem word32_back (x y : G) (t : Fin 3) (nil : L G 5=⊥)
    (z : trace x y false a=1) :
    pathAt x y (word32 t) 32=pathAt x y (word32 t) 0 := by
  change run x y (start G) ((wa t).take 32) = run x y (start G) []
  have e : (wa t).take 32=wa t := by fin_cases t <;> decide
  rw [e,(stop_word t x y nil).1,z]
  rfl

theorem word64_back (x y : G) (t : Fin 3) (nil : L G 5=⊥) :
    pathAt x y (word64 t) 64=pathAt x y (word64 t) 0 := by
  have e : (word64 t).toList.take 64=wa t++reverseWord (wb t) := by
    fin_cases t <;> decide
  have h := stop_word t x y nil
  unfold pathAt
  rw [e,List.take_zero]
  simp only [run,List.foldl_append]
  change run x y (run x y (start G) (wa t)) (reverseWord (wb t))=start G
  rw [h.1,←h.2,undo_run]

theorem at32 (x y : G) (t : Fin 3) (i : Fin 32) :
    pathAt x y (word32 t) i.val = vertAt x y t ⟨i.val,by have := i.isLt; omega⟩ := by
  have h : i.val≤32 := by have := i.isLt; omega
  simp [pathAt,word32,vertAt,wordAt,h]

set_option maxRecDepth 12000
set_option maxHeartbeats 0

private theorem layout (t : Fin 3) (i : Fin 64) :
    (word64 t).toList.take i.val =
      if i.val≤32 then wordAt t (reflIdx i)
      else wa t ++ reverseWord ((wb t).drop (64-i.val)) := by
  fin_cases t <;> decide +kernel +revert

theorem at64 (x y : G) (t : Fin 3) (i : Fin 64) (nil : L G 5=⊥) :
    pathAt x y (word64 t) i.val = vertAt x y t (reflIdx i) := by
  unfold pathAt vertAt
  rw [layout]
  split
  · rfl
  · rename_i LT
    have h := stop_word t x y nil
    simp only [run,List.foldl_append]
    change run x y (run x y (start G) (wa t)) (reverseWord ((wb t).drop (64-i.val))) = _
    rw [h.1,←h.2]
    have splitW : run x y (start G) (wb t) =
      run x y (run x y (start G) ((wb t).take (64-i.val))) ((wb t).drop (64-i.val)) := by
      simp only [run,←List.foldl_append,List.take_append_drop]
    rw [splitW,undo_run]
    have h' : (32 : Nat) < i.val := by omega
    have h'' : ¬96-i.val≤32 := by have := i.isLt; omega
    simp [wordAt,reflIdx,h',h'']
    congr 2
    have := i.isLt
    omega

end RibbonP3
#print axioms RibbonP3.at64
