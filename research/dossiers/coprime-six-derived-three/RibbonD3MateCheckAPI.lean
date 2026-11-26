import RibbonD3MateCheck

namespace RibbonD3MateData

theorem checkR_true (i : Fin charts.size) (j : Fin (charts[i]).rows.size) :
    checkR charts[i] (charts[i]).rows[j] = true := by
  have h := Array.all_eq_true.mp checkRAll_true i.val i.isLt
  exact Array.all_eq_true.mp h j.val j.isLt

#print axioms checkR_true
end RibbonD3MateData
