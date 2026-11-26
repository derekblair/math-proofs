import Ribbon6Chart
import RibbonP3Chart

namespace Ribbon6
open RibbonP3

def ptable : Array Row := ((rows wc.toList).take 64).toArray
def prow (i : Fin 64) : Row := ptable[i.val]?.getD zeroRow

def pkey (q t : Fin 3) (i : Fin 64) : Nat :=
  let r := prow i
  let c := (r.l + q.val*r.m + (r.k/3)*t.val)%3
  (if r.rim then 1 else 0) + 2*(r.i%3).toNat + 6*(r.j%3).toNat +
    18*(r.k%3).toNat + 54*c.toNat
def OK (q t : Fin 3) : Prop := (q.val+t.val)%3 ≠ 2
instance (q t : Fin 3) : Decidable (OK q t) := by unfold OK; infer_instance

def rep (i : Fin 64) : Fin 64 :=
  if h : 32 ≤ i.val ∧ (i.val ≤ 36 ∨ 60 ≤ i.val) then ⟨i.val-32,by omega⟩ else i
def reps : List (Fin 64) := (List.finRange 64).filter (fun i => rep i == i)

set_option maxRecDepth 16000
set_option maxHeartbeats 0
private def packed (q t : Fin 3) : Nat := (![![105571291088545340914571180009366196872236848867127595999590649298020845422351306773404526918883954990747838547704837360059067156865907563636990048796928,105571121853047460254662918793438091193120715389835617407007743052271300999400897583628640323743585554047533026035208262254148751073305213062393428246784,105570952625296565886899096070062941410733502481153957048262201955932644592596240333471710737189588605695816862053619532994401859273170562588726673604864],![105571121853047460254662918829273467750563210169873010863392724227600420714373465724251099703053931759434353845073609686352991982634306082599182980153600,105570952625296565886899096105898317968175997261191439434331436662432134741902523137244036458344042729964764731419712364279552381375909748729807295545600,105571291088545340914571180045201573429679343647164989457332589766769325036775082398686762842568916906675793882947742237386810358537343594542139710439680],![105570952625296565886899096141735322197560383051009210762699584000494771589328539183036710117809358267873921729446653865176519520932219827924765208543488,105571291088545340914571180081038577659063729436982760784343777811412601984749890959836786669162787204955452518428313931679296660897184167534028114428160,105571121853047460254662918865110471979947595959690871120088165803414068096681988948516735664463008081505666458947832423785472290390614645558362397016320]] q) t
private def fast (q t : Fin 3) (i : Fin 64) : Nat := (packed q t >>> (8*i.val)) &&& 255
private theorem fcorrect (q t : Fin 3) (i : Fin 64) : fast q t i = pkey q t i := by
  fin_cases q <;> fin_cases t <;> decide +revert
private theorem idem (i : Fin 64) : rep (rep i) = rep i := by decide +revert
private theorem mem_repr (i : Fin 64) : rep i ∈ reps := by simp [reps,idem]
private theorem repr_key (q t : Fin 3) (i : Fin 64) : fast q t (rep i)=fast q t i := by
  fin_cases q <;> fin_cases t <;> decide +revert
private theorem nodup_key (q t : Fin 3) (h : OK q t) :
    (reps.map (fast q t)).Nodup := by
  fin_cases q <;> fin_cases t <;> revert h <;> decide
private theorem role (i j : Fin 64) (l : i.val<j.val) (h : rep i=rep j) :
    same i.val j.val := by
  unfold rep at h
  split at h <;> split at h <;> have E := congrArg Fin.val h <;> (try simp only [Fin.val_mk] at E) <;> unfold same <;> omega
theorem p3chart (q t : Fin 3) (h : OK q t) (i j : Fin 64) (l : i.val<j.val)
    (H : pkey q t i = pkey q t j) : same i.val j.val := by
  apply role i j l
  apply List.inj_on_of_nodup_map (nodup_key q t h) (mem_repr i) (mem_repr j)
  rw [repr_key,repr_key,fcorrect,fcorrect]
  exact H

theorem p3case (q t : Fin 3) : OK q t ∨ OK (-q) (-t) := by decide +revert

end Ribbon6
#print axioms Ribbon6.p3chart
