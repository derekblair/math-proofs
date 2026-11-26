import HaarClass5P3MetaCore

namespace HaarClass5P3Meta
open HaarClass4Data
variable {G : Type*} [Group G] (M : Model G)

def term (i : ℤ) : Triple := if i=-1 then (-1,1,0) else if i=0 then (0,0,0)
  else if i=1 then (1,0,0) else (2,7,1)

def negTriple (p : Triple) : Triple := (-p.1,-p.2.1,-p.2.2)

theorem dneg (p : Triple) : D M (negTriple p)=(D M p)⁻¹ := by
  have h := dadd M p (negTriple p)
  have e : tripAdd p (negTriple p)=(0,0,0) := by
    rcases p with ⟨a,b,c⟩
    simp [tripAdd,negTriple]
  rw [e] at h
  have g : D M p*D M (negTriple p)=1 := by simpa [D] using h.symm
  exact eq_inv_of_mul_eq_one_right g

theorem rightxc : rc M.x M.c = D M (1,7,1) := by
  have h := leftX_eval M (1,7,1)
  have v : cap (leftX (1,7,1)) = (1,0,0) := by decide
  rw [←dcap M (leftX (1,7,1)),v] at h
  have h' : M.x*D M (1,7,1)*M.x⁻¹=M.c := by simpa [rc,D] using h
  change M.x⁻¹*M.c*M.x = _
  rw [←h']
  group

theorem term_eval (i : ℤ) (r : i=-1 ∨ i=0 ∨ i=1 ∨ i=2) :
    M.x^i*M.y=M.y*M.x^i*D M (term i) := by
  rcases r with h|h|h|h <;> subst i
  · have E : D M (term (-1))=M.x*M.c⁻¹*M.x⁻¹ := by
      have h : M.x*M.c*M.x⁻¹=M.c*M.u⁻¹ := by simpa [rc] using M.xc
      have e := congrArg (fun g : G => g⁻¹) h
      simp only [mul_inv_rev,inv_inv] at e
      simp only [term,ite_true,D,zpow_neg_one,zpow_one,zpow_zero,mul_one]
      rw [mul_assoc,e,(M.cu.inv_left).eq]
    simp only [zpow_neg_one,E]
    have h := M.xy
    have e : M.x⁻¹*M.y=M.y*M.c⁻¹*M.x⁻¹ := by
      have f := congrArg (fun z : G => M.x⁻¹*z*M.c⁻¹*M.x⁻¹) h
      simpa [mul_assoc] using f.symm
    rw [e]
    group
  · simp [term,D]
  · simpa [term,D] using M.xy
  · have E : D M (term 2) = D M (1,7,1)*M.c := by
      rw [←show D M (1,0,0)=M.c by simp [D],←dadd]
      rfl
    norm_num [E,pow_two]
    calc
      M.x*M.x*M.y = M.x*(M.x*M.y) := by rw [mul_assoc]
      _ = M.y*(M.x*M.x)*(D M (1,7,1)*M.c) := by
        rw [M.xy]
        simp only [mul_assoc]
        rw [←mul_assoc M.x M.y _,M.xy]
        have b := rightxc M
        change M.x⁻¹*M.c*M.x = _ at b
        rw [←b]
        group

def normRow (r : Row) : Row := (r.1,r.2.1,cap r.2.2)

def negX (r : Row) : Row := normRow (r.1-1,r.2.1,leftX r.2.2)
def negY (r : Row) : Row := normRow (r.1,r.2.1-1,leftY (tripAdd r.2.2 (negTriple (term r.1))))

theorem negX_eval (r : Row) : eval M (negX r)*M.x=eval M r := by
  simp only [eval,negX,normRow,dcap,←leftX_eval,zpow_sub_one]
  simp only [rc,MonoidHom.coe_mk,OneHom.coe_mk,inv_inv]
  group

theorem negY_eval (r : Row) (hi : r.1=-1 ∨ r.1=0 ∨ r.1=1 ∨ r.1=2) :
    eval M (negY r)*M.y=eval M r := by
  have H := term_eval M r.1 hi
  simp only [eval,negY,normRow,dcap,←leftY_eval,zpow_sub_one,dadd,dneg]
  simp only [rc,MonoidHom.coe_mk,OneHom.coe_mk,inv_inv]
  calc
    _ = M.y^r.2.1*M.y⁻¹*(M.x^r.1*M.y)*(D M r.2.2*(D M (term r.1))⁻¹) := by group
    _ = M.y^r.2.1*M.x^r.1*(D M (term r.1)*(D M r.2.2*(D M (term r.1))⁻¹)) := by rw [H]; group
    _ = _ := by
      have cd : Commute (D M (term r.1)) (D M r.2.2) := by
        change D M (term r.1)*D M r.2.2 = D M r.2.2*D M (term r.1)
        rw [←dadd,←dadd]
        congr 1
        simp [tripAdd,add_comm]
      rw [←mul_assoc (D M (term r.1)) (D M r.2.2),cd.eq]
      group

end HaarClass5P3Meta
