import HaarClass5P3MetaSteps
import HaarClassFourFinite

namespace HaarClass5P3Meta
open HaarAllNoncommuting
variable {G H : Type*} [Group G] [Group H]

def tab (i : Fin 32) : Row := (#[
  (0, 0, 0, 0, 0), (0, 0, 0, 0, 0), (0, -1, 0, 0, 0), (1, -1, 0, 0, 0),
  (1, -1, 0, 0, 0), (1, 0, 1, 0, 0), (0, 0, 1, 8, 0), (0, 1, 1, 7, 1),
  (0, 1, 1, 7, 1), (0, 2, 1, 0, 0), (-1, 2, 1, 8, 0), (-1, 2, 1, 8, 0),
  (-1, 1, 2, 0, 0), (0, 1, 2, 5, 2), (0, 0, 2, 7, 0), (1, 0, 2, 0, 0),
  (1, 0, 2, 0, 0), (1, 1, 3, 7, 0), (0, 1, 3, 4, 2), (0, 1, 3, 4, 2),
  (-1, 1, 3, 7, 1), (-1, 2, 2, 8, 0), (-1, 2, 2, 8, 0), (0, 2, 2, 7, 1),
  (0, 1, 2, 6, 1), (1, 1, 2, 8, 0), (1, 1, 2, 8, 0), (2, 1, 2, 7, 1),
  (2, 0, 0, 0, 0), (2, 0, 0, 0, 0), (1, 0, 0, 0, 0), (1, 0, 0, 0, 0)] : Array Row)[i.val]!
def side (i : Fin 32) : Bool := decide (i.val%2=1)
def rang (p : Row) : Prop := p.1=-1 ∨ p.1=0 ∨ p.1=1 ∨ p.1=2
instance (p : Row) : Decidable (rang p) := by unfold rang; infer_instance

def Adj (l r : Row) : Prop := l=r ∨ l=negX r ∨ (l=negY r ∧ rang r)
instance (l r : Row) : Decidable (Adj l r) := by unfold Adj; infer_instance

theorem tab_edge (i : Fin 32) : side i ≠ side (i+1) ∧
    (if side i then Adj (tab (i+1)) (tab i) else Adj (tab i) (tab (i+1))) := by
  revert i
  decide

def vert (M : Model G) (i : Fin 32) : Bool×G := (side i,eval M (tab i))

theorem vert_adj (M : Model G) (i : Fin 32) :
    HaarCycle.haarAdj M.x M.y (vert M i) (vert M (i+1)) := by
  obtain ⟨h,t⟩ := tab_edge i
  have z (l r : Row) (e : Adj l r) :
      eval M r=eval M l ∨ eval M r=eval M l*M.x ∨ eval M r=eval M l*M.y := by
    rcases e with h|h|⟨h,b⟩
    · exact Or.inl (congrArg _ h.symm)
    · exact Or.inr (Or.inl (by rw [h,negX_eval]))
    · exact Or.inr (Or.inr (by rw [h,negY_eval M r b]))
  cases hi : side i <;> cases hj : side (i+1) <;> simp [hi,hj] at h t
  · simpa [HaarCycle.haarAdj,vert,hi,hj] using z _ _ t
  · simpa [HaarCycle.haarAdj,vert,hi,hj] using z _ _ t

def sep (i j : Fin 32) : Prop :=
  let p := tab i
  let q := tab j
  i=j ∨ side i ≠ side j ∨
    (p.1-q.1)%3≠0 ∨ (p.2.1-q.2.1)%3≠0 ∨
    (p.1=q.1 ∧ p.2.1=q.2.1 ∧ (p.2.2.1-q.2.2.1)%3≠0) ∨
    (p.1=q.1 ∧ p.2.1=q.2.1 ∧ p.2.2.1=q.2.2.1 ∧
      ((p.2.2.2.1-q.2.2.2.1)%9≠0 ∨ (p.2.2.2.2-q.2.2.2.2)%3≠0))

instance (i j : Fin 32) : Decidable (sep i j) := by unfold sep; infer_instance

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem tab_sep (i j : Fin 32) : sep i j := by revert i j; decide

theorem mob (c : H) (h3 : 3 ∣ orderOf c) {a b : ℤ} (eq : c^a=c^b) : (a-b)%3=0 := by
  have z : c^(a-b)=1 := by rw [zpow_sub,eq,mul_inv_cancel]
  have dd := Int.natCast_dvd_natCast.mpr h3
  exact Int.emod_eq_zero_of_dvd (dd.trans (orderOf_dvd_iff_zpow_eq_one.mpr z))

theorem tail_reduce (M : Model G) (u9 : orderOf M.u=9) (notin : M.A ∉ Subgroup.zpowers M.u)
    (a b c d : ℤ) (e : M.u^a*M.A^b=M.u^c*M.A^d) :
    (a-c)%9=0 ∧ (b-d)%3=0 := by
  have ez : M.u^(a-c)*M.A^(b-d)=1 := by
    rw [zpow_sub,zpow_sub]
    have sw := ((M.ua.zpow_zpow c b).inv_left).eq
    calc
      _ = M.u^a*((M.u^c)⁻¹*M.A^b)*(M.A^d)⁻¹ := by simp only [mul_assoc]
      _ = (M.u^a*M.A^b)*((M.u^c)⁻¹*(M.A^d)⁻¹) := by rw [sw]; simp only [mul_assoc]
      _ = (M.u^c*M.A^d)*((M.A^d)⁻¹*(M.u^c)⁻¹) := by
        rw [e,((M.ua.zpow_zpow c d).inv_left.inv_right).eq]
      _ = 1 := by rw [←mul_inv_rev,mul_inv_cancel]
  have d3 : M.A^(3:ℤ)=1 := by exact_mod_cast M.A3
  have d2 : M.A^(b-d) ∈ Subgroup.zpowers M.u := by
    have h := eq_inv_of_mul_eq_one_right ez
    rw [h]
    exact (Subgroup.zpowers M.u).inv_mem (Subgroup.zpow_mem_zpowers _ _)
  rw [←pow_mod M.A 3 d3] at d2
  have z : (b-d)%3=0 := by
    have bounds : 0≤(b-d)%3 ∧ (b-d)%3<3 := by omega
    obtain h|h|h : (b-d)%3=0 ∨ (b-d)%3=1 ∨ (b-d)%3=2 := by omega
    · exact h
    · exfalso
      apply notin
      simpa [h] using d2
    · exfalso
      apply notin
      rw [h] at d2
      have sq := (Subgroup.zpowers M.u).pow_mem d2 2
      have cc : (M.A^(2:ℤ))^(2:ℕ)=M.A := by
        rw [show (2:ℤ)=↑(2:ℕ) by decide,zpow_natCast,←pow_mul,show (2:ℕ)*2=3+1 by decide,pow_succ,M.A3,one_mul]
      rwa [cc] at sq
  rw [←pow_mod M.A 3 d3 (b-d),z,zpow_zero,mul_one] at ez
  have dd := orderOf_dvd_iff_zpow_eq_one.mpr ez
  rw [u9] at dd
  exact ⟨Int.emod_eq_zero_of_dvd dd,z⟩

theorem cycle32 (M : Model G) (φ : G →* H)
    (killU : φ M.u=1) (killA : φ M.A=1)
    (cx : Commute (φ M.c) (φ M.x)) (cy : Commute (φ M.c) (φ M.y))
    (div3 : 3 ∣ orderOf (φ M.c)) (u9 : orderOf M.u=9)
    (notin : M.A ∉ Subgroup.zpowers M.u) :
    HasCycle M.x M.y 32 := by
  refine cycle_form (vert M) ?_ (vert_adj M)
  intro i j he
  let p := tab i
  let q := tab j
  have H : eval M p=eval M q := congrArg Prod.snd he
  have proj (r : Row) :
      φ (eval M r)=HaarCycle.norm (φ M.x) (φ M.y) (φ M.c) (r.1,r.2.1,r.2.2.1) := by
    simp [eval,D,killU,killA,HaarCycle.norm]
  have E := (proj p).symm.trans ((congrArg φ H).trans (proj q))
  have r : φ M.x*φ M.y=φ M.y*φ M.x*φ M.c := by
    have h := congrArg φ M.xy
    simpa only [map_mul] using h
  obtain ⟨hi,hj⟩ := HaarBound16.conjugate_eq _ _ _ cx cy r E
  rcases tab_sep i j with eq|s|hI|hJ|⟨a,b,c⟩|⟨a,b,c,t⟩
  · exact eq
  · exact False.elim (s (congrArg Prod.fst he))
  · exact False.elim (hI (mob _ div3 hi))
  · exact False.elim (hJ (mob _ div3 hj))
  · exfalso
    apply c
    apply mob _ div3
    change (φ M.y)^p.2.1*(φ M.x)^p.1*(φ M.c)^p.2.2.1 =
      (φ M.y)^q.2.1*(φ M.x)^q.1*(φ M.c)^q.2.2.1 at E
    change p.1=q.1 at a
    change p.2.1=q.2.1 at b
    rw [a,b] at E
    exact mul_left_cancel E
  · exfalso
    change p.1=q.1 at a
    change p.2.1=q.2.1 at b
    change p.2.2.1=q.2.2.1 at c
    simp only [eval,D,mul_assoc] at H
    rw [a,b,c] at H
    have e := tail_reduce M u9 notin _ _ _ _ (mul_left_cancel (mul_left_cancel (mul_left_cancel H)))
    rcases t with d|d
    · exact d e.1
    · exact d e.2

end HaarClass5P3Meta
#print axioms HaarClass5P3Meta.cycle32
