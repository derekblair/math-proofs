import GeometricCompact
import GeometricAttachment

namespace RobustFolkman.GeometricGap
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def pageCol (v : I→ℝ) : Matrix I Unit ℝ := fun i _ => v i

def pageBorder (A : Matrix I I ℝ) (c : I→ℝ) : Matrix (I⊕Unit) (I⊕Unit) ℝ :=
  Matrix.fromBlocks A (pageCol c) (pageCol c)ᴴ 1

theorem page_schur (A : Matrix I I ℝ) [Invertible A] (sym : A.IsHermitian) (v : I→ℝ) :
    let B := pageCol (A *ᵥ v)
    (Bᴴ*⅟A*B) () () = A.toBilin' v v := by
  intro B
  let R : Matrix Unit I ℝ := fun _ i => v i
  have cb : B=A*pageCol v := by rfl
  have rb : Bᴴ=R*A := by
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial,cb,Matrix.mul_apply,pageCol,R]
    apply Finset.sum_congr rfl
    intro k _
    have h := congrFun (congrFun sym.eq j) k
    have e : A k j=A j k := by simpa [Matrix.conjTranspose_apply] using h
    change A j k*v k=v k*A k j
    rw [e,mul_comm]
  have red : (R*A)*⅟A*(A*pageCol v)=R*(A*pageCol v) := by simp [Matrix.mul_assoc]
  rw [rb,cb,red,Matrix.toBilin'_apply]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [R,pageCol]
  ring

theorem scalar_psd (D : Matrix Unit Unit ℝ) : D.PosSemidef ↔ 0≤D () () := by
  constructor
  · exact fun h => h.diag_nonneg (i:=())
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      cases i
      cases j
      simp [Matrix.conjTranspose_apply]
    · intro v
      simp only [star_trivial,Matrix.mulVec,dotProduct,Fintype.sum_unique]
      change 0≤ v () * (D () () * v ())
      calc
        0 ≤ D () ()*(v ())^2 := mul_nonneg h (sq_nonneg _)
        _ = _ := by ring

theorem page_bounds_det (A : Matrix I I ℝ) [Invertible A] (pd : A.PosDef) (v : I→ℝ) :
    (pageBorder A (A *ᵥ v)).det=A.det*(1-A.toBilin' v v) := by
  rw [pageBorder,Matrix.det_fromBlocks₁₁,Matrix.det_unique
    (1-(pageCol (A *ᵥ v))ᴴ*⅟A*(pageCol (A *ᵥ v)))]
  congr 1
  rw [Matrix.sub_apply, Matrix.one_apply_eq, page_schur A pd.isHermitian v]

theorem page_bounds_psd (A : Matrix I I ℝ) [Invertible A] (pd : A.PosDef) (v : I→ℝ) :
    (pageBorder A (A *ᵥ v)).PosSemidef ↔ A.toBilin' v v≤1 := by
  rw [pageBorder, Matrix.PosDef.fromBlocks₁₁ _ _ pd, scalar_psd, Matrix.sub_apply, Matrix.one_apply_eq]
  rw [←Matrix.invOf_eq_nonsing_inv, page_schur A pd.isHermitian v]
  exact sub_nonneg

theorem page_achieves_exact (A : Matrix I I ℝ) (pd : A.PosDef)
    (i j : I) (di : A i i=1) (dj : A j j=1) (r t : ℝ) (rij : A i j=r)
    (r0 : 0<1+r) (t0 : 0≤t) (f0 : 0≤1-2*t^2/(1+r)) :
    (∀ c, t≤c i → t≤c j → (pageBorder A c).det≤A.det*(1-2*t^2/(1+r))) ∧
    (∃ c, c i=t ∧ c j=t ∧ (pageBorder A c).PosSemidef ∧
      (pageBorder A c).det=A.det*(1-2*t^2/(1+r))) := by
  let _ : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr pd.det_pos.ne')
  let x : I → ℝ := Pi.single i 1
  let y : I → ℝ := Pi.single j 1
  have sym : ∀ i j, A i j=A j i := by
    intro i j
    have h := congrFun (congrFun pd.isHermitian.eq i) j
    simpa [Matrix.conjTranspose_apply] using h.symm
  have bs (x y : I→ℝ) : A.toBilin' x y=A.toBilin' y x := by
    rw [Matrix.toBilin'_apply,Matrix.toBilin'_apply,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [sym j i]
    ring
  have psd : ∀ v : I→ℝ, 0≤A.toBilin' v v := by
    intro v
    simpa [Matrix.toBilin'_apply'] using pd.posSemidef.dotProduct_mulVec_nonneg v
  have Axi (v : I→ℝ) : A.toBilin' x v=(A *ᵥ v) i := by
    rw [Matrix.toBilin'_apply']
    simp [x,single_dotProduct]
  have Ayj (v : I→ℝ) : A.toBilin' y v=(A *ᵥ v) j := by
    rw [Matrix.toBilin'_apply']
    simp [y,single_dotProduct]
  obtain ⟨upper,attained⟩ := attaching_triangle_quadratic A.toBilin' bs
    psd x y r t (by simpa [x] using di) (by simpa [y] using dj)
    (by simpa [x,y] using rij) r0 t0
  refine ⟨?_,?_⟩
  · intro c ci cj
    let v := (⅟A) *ᵥ c
    have vc : A *ᵥ v=c := by unfold v; rw [Matrix.mulVec_mulVec]; simp
    rw [←vc, page_bounds_det A pd v]
    have hx : t≤A.toBilin' x v := by rwa [Axi,vc]
    have hy : t≤A.toBilin' y v := by rwa [Ayj,vc]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left (upper v hx hy) _) pd.det_pos.le
  · obtain ⟨v,vi,vj,vv⟩ := attained
    rw [Axi] at vi
    rw [Ayj] at vj
    refine ⟨A *ᵥ v,vi,vj,?_,by rw [page_bounds_det A pd v,vv]⟩
    rw [page_bounds_psd A pd v,vv]
    exact sub_nonneg.mp f0

#print axioms page_achieves_exact
end RobustFolkman.GeometricGap
