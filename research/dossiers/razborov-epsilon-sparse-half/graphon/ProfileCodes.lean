import ProfileAtoms

open MeasureTheory Set Function
namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]
variable (ν : Measure X) [IsFiniteMeasure ν]

/-- Countably many anchor-cell integrals encode a row. This avoids
requiring measurability into L1 itself. For a generating pi-system
row uniqueness is a separate finite-measure extensionality argument. -/
noncomputable def profileCode (T : ℕ→Set X) (K : Kernel X) (x : X) (n:ℕ) :=
  deg (ν.restrict (T n)) K x

noncomputable def codeFlip (T : ℕ→Set X) (p : ℕ→ℝ) (n : ℕ) :=
  mass (ν.restrict (T n))-p n

lemma profileCode_meas (T : ℕ→Set X) (K : Kernel X) :
    Measurable (profileCode ν T K) := by
  apply Measurable.of_eval
  intro n
  exact deg_measurable (ν.restrict (T n)) K

lemma codeFlip_meas (T : ℕ→Set X) : Measurable (codeFlip ν T) := by
  apply Measurable.of_eval
  intro n
  exact measurable_const.sub (measurable_pi_apply n)

lemma codeFlip_inv (T : ℕ→Set X) (p : ℕ→ℝ) :
    codeFlip ν T (codeFlip ν T p)=p := by
  funext n
  unfold codeFlip
  ring

theorem indicator_rows_codes (T : ℕ→Set X) (K : Kernel X) (x y:X)
    (h : ∀ᵐ z ∂ν, (K.W (x,z)=0 ∧ K.W (y,z)=1) ∨ (K.W (x,z)=1 ∧ K.W (y,z)=0)) :
    profileCode ν T K y=codeFlip ν T (profileCode ν T K x) := by
  funext n
  let m := ν.restrict (T n)
  have hz : ∀ᵐ z ∂m, K.W (x,z)+K.W (y,z)=1 := by
    filter_upwards [h.filter_mono (Measure.restrict_le_self (s:=T n)).absolutelyContinuous.ae_le] with z hz
    rcases hz with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> simp [h₁,h₂]
  have he := integral_congr_ae hz
  rw [integral_add (row_integrable m K x) (row_integrable m K y),integral_const,smul_eq_mul,mul_one] at he
  change deg m K x+deg m K y=mass m at he
  change deg m K y=mass m-deg m K x
  linarith

#print axioms profileCode_meas
#print axioms indicator_rows_codes
end SparseHalfGraphon
