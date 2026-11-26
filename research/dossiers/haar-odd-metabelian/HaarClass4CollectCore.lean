import HaarClass4Table

namespace HaarClass4CollectCore

variable {G : Type*} [Group G]

def Central (a : G) : Prop := ∀ g : G, Commute a g

theorem move_right (x c u v A B : G)
    (ccu : Commute c u)
    (hA : Central A) (hB : Central B)
    (cx : c*x=x*c*(u*A)) (ux : u*x=x*u*A) (vx : v*x=x*v*B)
    (k a b : ℤ) :
    (c^k*u^a*v^b)*x = x*(c^k*u^(a+k)*v^b)*(A^(a+k)*B^b) := by
  have hx := HaarCycle.shift c x (u*A) (ccu.symm.mul_left (hA c)) cx k
  have hu := HaarCycle.shift u x A (hA u) ux a
  have hv := HaarCycle.shift v x B (hB v) vx b
  have hcA := (hA u).symm.mul_zpow k
  calc
    (c^k*u^a*v^b)*x = c^k*(u^a*(v^b*x)) := by simp only [mul_assoc]
    _ = c^k*(u^a*x)*v^b*B^b := by rw [hv]; simp only [mul_assoc]
    _ = (c^k*x)*u^a*A^a*v^b*B^b := by rw [hu]; simp only [mul_assoc]
    _ = x*c^k*((u*A)^k)*u^a*A^a*v^b*B^b := by rw [hx]
    _ = x*(c^k*u^(a+k)*v^b)*(A^(a+k)*B^b) := by
      rw [hcA,zpow_add,zpow_add]
      simp only [mul_assoc]
      rw [← mul_assoc (A^k) (u^a),((hA u).zpow_zpow k a).eq, mul_assoc (u^a) (A^k)]
      rw [← mul_assoc (A^a) (v^b),((hA v).zpow_zpow a b).eq,mul_assoc (v^b) (A^a)]
      rw [← mul_assoc (A^k) (v^b),((hA v).zpow_zpow k b).eq,mul_assoc (v^b) (A^k)]
      rw [← mul_assoc (u^k) (u^a),((Commute.refl u).zpow_zpow k a).eq]
      rw [← mul_assoc (A^k) (A^a),((Commute.refl A).zpow_zpow k a).eq]
      simp only [mul_assoc]

theorem move_right_y (y c u v B C : G)
    (ccv : Commute c v) (cuv : Commute u v)
    (hB : Central B) (hC : Central C)
    (cy : c*y=y*c*(v*C)) (uy : u*y=y*u*B) (vy : v*y=y*v*C)
    (k a b : ℤ) :
    (c^k*u^a*v^b)*y = y*(c^k*u^a*v^(b+k))*(B^a*C^(b+k)) := by
  have hy := HaarCycle.shift c y (v*C) (ccv.symm.mul_left (hC c)) cy k
  have hu := HaarCycle.shift u y B (hB u) uy a
  have hv := HaarCycle.shift v y C (hC v) vy b
  calc
    (c^k*u^a*v^b)*y = c^k*(u^a*(v^b*y)) := by simp only [mul_assoc]
    _ = c^k*(u^a*y)*v^b*C^b := by rw [hv]; simp only [mul_assoc]
    _ = (c^k*y)*u^a*B^a*v^b*C^b := by rw [hu]; simp only [mul_assoc]
    _ = y*c^k*((v*C)^k)*u^a*B^a*v^b*C^b := by rw [hy]
    _ = y*(c^k*u^a*v^(b+k))*(B^a*C^(b+k)) := by
      rw [(hC v).symm.mul_zpow k,zpow_add,zpow_add]
      simp only [mul_assoc]
      rw [← mul_assoc (C^k) (u^a),((hC u).zpow_zpow k a).eq,mul_assoc (u^a) (C^k)]
      rw [← mul_assoc (v^k) (u^a),((cuv.symm).zpow_zpow k a).eq,mul_assoc (u^a) (v^k)]
      rw [← mul_assoc (B^a) (v^b),((hB v).zpow_zpow a b).eq,mul_assoc (v^b) (B^a)]
      rw [← mul_assoc (C^k) (v^b),((hC v).zpow_zpow k b).eq,mul_assoc (v^b) (C^k)]
      rw [← mul_assoc (v^k) (v^b),((Commute.refl v).zpow_zpow k b).eq,mul_assoc (v^b) (v^k)]
      rw [← mul_assoc (C^k) (B^a),((hC B).zpow_zpow k a).eq,mul_assoc (B^a) (C^k)]
      rw [((Commute.refl C).zpow_zpow k b).eq]

end HaarClass4CollectCore

#print axioms HaarClass4CollectCore.move_right
#print axioms HaarClass4CollectCore.move_right_y
