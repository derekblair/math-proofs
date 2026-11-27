import NeutralFixedPoint

namespace IntegerEigen
open NeutralTrace

def mat (a b c d : ℤ) : (ℤ×ℤ) →+ (ℤ×ℤ) where
  toFun p := (a*p.1+b*p.2,c*p.1+d*p.2)
  map_zero' := by simp
  map_add' p q := by ext <;> simp <;> ring

def eigvec (a b c d r : ℤ) : ℤ×ℤ :=
  if a=r ∧ c=0 then (r-d,b) else (c,r-a)

theorem is_eig (a b c d r : ℤ) (h : (a-r)*(d-r)-b*c=0) (p : ℤ×ℤ) :
    pro (eigvec a b c d r) (mat a b c d p) = r*pro (eigvec a b c d r) p := by
  unfold eigvec
  split
  · rename_i he
    rcases he with ⟨rfl,rfl⟩
    simp [pro,mat]
    ring
  · simp only [pro,mat,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
    linear_combination (-p.2)*h

theorem nonzero (a b c d r t : ℤ) (hd : r≠t) (ht : (a-t)*(d-t)-b*c=0) :
    eigvec a b c d r ≠ 0 := by
  unfold eigvec
  split
  · rename_i he
    obtain ⟨ha,hc⟩ := he
    intro hg
    have h1 : r-d=0 := congrArg Prod.fst hg
    have h2 : b=0 := congrArg Prod.snd hg
    have hh : d=r := by omega
    simp [ha,hc,hh,h2] at ht
    exact hd (by omega)
  · rename_i he
    intro hg
    have h1 : c=0 := congrArg Prod.fst hg
    have h2 : r-a=0 := congrArg Prod.snd hg
    exact he ⟨by omega,h1⟩

theorem independent (A : (ℤ×ℤ) → (ℤ×ℤ)) (u v : ℤ×ℤ) (r t : ℤ)
    (hd : r≠t) (un : u≠0) (vn : v≠0)
    (hu : ∀ p, pro u (A p)=r*pro u p)
    (hv : ∀ p, pro v (A p)=t*pro v p) :
    u.1*v.2-u.2*v.1 ≠ 0 := by
  intro w
  have hsum (p : ℤ×ℤ) : u.1*pro v p = v.1*pro u p := by
    simp only [pro]
    linear_combination p.2*w
  have hsum₂ (p : ℤ×ℤ) : u.2*pro v p = v.2*pro u p := by
    simp only [pro]
    linear_combination (-p.1)*w
  by_cases h : u.1=0
  · have uh : u.2≠0 := fun q => un (Prod.ext h q)
    have hV : v.1=0 := by
      rw [h,zero_mul,zero_sub,neg_eq_zero] at w
      exact (mul_eq_zero.mp w).resolve_left uh
    have vh : v.2≠0 := fun q => vn (Prod.ext hV q)
    have p := hsum₂ (A (0,1))
    rw [hv,hu] at p
    simp [pro] at p
    have e : u.2*v.2*(t-r)=0 := by linear_combination p
    exact hd (by
      have eq := (mul_eq_zero.mp e).resolve_left (mul_ne_zero uh vh)
      omega)
  · have hV : v.1≠0 := by
      intro hv
      rw [hv,mul_zero,sub_zero] at w
      exact vn (Prod.ext hv ((mul_eq_zero.mp w).resolve_left h))
    have p := hsum (A (1,0))
    rw [hv,hu] at p
    simp [pro] at p
    have e : u.1*v.1*(t-r)=0 := by linear_combination p
    exact hd (by
      have eq := (mul_eq_zero.mp e).resolve_left (mul_ne_zero h hV)
      omega)

end IntegerEigen

#print axioms IntegerEigen.is_eig
#print axioms IntegerEigen.nonzero
#print axioms IntegerEigen.independent
