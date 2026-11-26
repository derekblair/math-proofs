from pathlib import Path
start='''import RibbonStationarySlopeFinalCore
'''+''.join('import RibbonStationaryModData'+str(i)+'\n' for i in range(10))+'''
namespace RibbonStationaryField
open RibbonStationaryWord
open RibbonAffine (pl)
variable {K : Type*} [Field K]

theorem slope_pack (r : Fin 76) : ∃ C : Cover, RowValid (branch r.val).p C ∧ GeomValid (branch r.val) C ∧
    ∀ k : Fin C.rows.size, ∃ p : PrimeCert, primeValid (branch r.val).p C.rows[k] p := by
  let a := r.val/8
  let b := r.val%8
  have qa : a≤9 := by have := r.isLt; dsimp [a]; omega
  have qb : b<8 := by dsimp [b]; omega
  have e : r.val=8*a+b := by dsimp [a,b]; omega
  interval_cases h : a
'''
for i in range(10):
 start+=f'''  · have eq : r.val={i*8}+b := by simpa [h] using e
'''
 if i==9:start+='    have qb : b<4 := by have := r.isLt; omega\n'
 start+=f'''    let s : Fin {8 if i<9 else 4} := ⟨b,qb⟩
    rw [eq]
    refine ⟨data{i}[s.val]!, valid{i} s, geom{i} s, ?_⟩
    intro k
    exact ⟨mp{i} s k.val,modProof{i} s k⟩
'''
start+='''
theorem slope_full (r : Fin 76) (t : Kˣ) (n : Nat) (two : (2:K)≠0) (odd : Odd n) (no3 : ¬3∣n)
    (tn : t^n=1) (nt : t≠1) (F : pl t 1 (branch r.val).p=0) :
    (∃ k : Count, separates (t^(branch r.val).v) (t^(-(branch r.val).u)) k) ∨
      ((11:K)=0 ∧ ((t:K)=3 ∨ (t:K)=4 ∨ (t:K)=5 ∨ (t:K)=9)) := by
  obtain ⟨C,R,G,M⟩ := slope_pack r
  exact (slope_use _ C R G M t n two odd no3 tn nt F).imp_left (fun h => ⟨_,h⟩)

end RibbonStationaryField
#print axioms RibbonStationaryField.slope_full
'''
Path('RibbonStationarySlopeFinal.lean').write_text(start)
