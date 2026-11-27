import HaarAbelCore

namespace HaarAbel
open HaarAbelCore HaarAllNoncommuting
variable {G : Type*} [Group G]
variable (x y : G) (c : Commute x y)
include c
def lastIdx (n : ℕ) : Fin (n+1) := ⟨n,by omega⟩
def w0 : Fin 5 → P := fun i => (#[(0,0), (0,0), (0,-1), (0,-1), (0,-2)] : Array P)[i.val]!
def w0diff : List P := [(0,1)]
theorem w0case (f0 : ¬R x y (0,1)) (f1 : ¬R x y (1,-1)) (f2 : ¬R x y (1,0))
    (r : R x y (0,2)) : HasCycle x y 4 ∨ HasCycle x y 8 := by
  have clos : image x y (w0 (lastIdx 4)) = image x y (w0 ⟨0,by decide⟩) := by
    change image x y (0,-2) = image x y (0:P)
    rw [image_zero]
    exact negR x y c (0,2) r
  left
  refine chain (n:=4) (by decide) (by decide) x y c w0 w0diff (by decide) (by decide) clos ?_
  intro p hp
  simp [w0diff] at hp
  rcases hp with rfl
  · exact f0
def w1 : Fin 5 → P := fun i => (#[(0,0), (0,0), (0,-1), (1,-1), (1,-2)] : Array P)[i.val]!
def w1diff : List P := [(0,1), (1,-1)]
theorem w1case (f0 : ¬R x y (0,1)) (f1 : ¬R x y (1,-1)) (f2 : ¬R x y (1,0))
    (r : R x y (1,-2)) : HasCycle x y 4 ∨ HasCycle x y 8 := by
  have clos : image x y (w1 (lastIdx 4)) = image x y (w1 ⟨0,by decide⟩) := by
    change image x y (1,-2) = image x y (0:P)
    rw [image_zero]
    exact r
  left
  refine chain (n:=4) (by decide) (by decide) x y c w1 w1diff (by decide) (by decide) clos ?_
  intro p hp
  simp [w1diff] at hp
  rcases hp with rfl | rfl
  · exact f0
  · exact f1
def w2 : Fin 5 → P := fun i => (#[(0,0), (0,0), (-1,0), (-1,0), (-1,-1)] : Array P)[i.val]!
def w2diff : List P := [(1,0)]
theorem w2case (f0 : ¬R x y (0,1)) (f1 : ¬R x y (1,-1)) (f2 : ¬R x y (1,0))
    (r : R x y (1,1)) : HasCycle x y 4 ∨ HasCycle x y 8 := by
  have clos : image x y (w2 (lastIdx 4)) = image x y (w2 ⟨0,by decide⟩) := by
    change image x y (-1,-1) = image x y (0:P)
    rw [image_zero]
    exact negR x y c (1,1) r
  left
  refine chain (n:=4) (by decide) (by decide) x y c w2 w2diff (by decide) (by decide) clos ?_
  intro p hp
  simp [w2diff] at hp
  rcases hp with rfl
  · exact f2
def w4 : Fin 5 → P := fun i => (#[(0,0), (1,0), (1,-1), (2,-1), (2,-2)] : Array P)[i.val]!
def w4diff : List P := [(1,-1)]
theorem w4case (f0 : ¬R x y (0,1)) (f1 : ¬R x y (1,-1)) (f2 : ¬R x y (1,0))
    (r : R x y (2,-2)) : HasCycle x y 4 ∨ HasCycle x y 8 := by
  have clos : image x y (w4 (lastIdx 4)) = image x y (w4 ⟨0,by decide⟩) := by
    change image x y (2,-2) = image x y (0:P)
    rw [image_zero]
    exact r
  left
  refine chain (n:=4) (by decide) (by decide) x y c w4 w4diff (by decide) (by decide) clos ?_
  intro p hp
  simp [w4diff] at hp
  rcases hp with rfl
  · exact f1
def w5 : Fin 5 → P := fun i => (#[(0,0), (0,0), (-1,0), (-1,1), (-2,1)] : Array P)[i.val]!
def w5diff : List P := [(1,-1), (1,0)]
theorem w5case (f0 : ¬R x y (0,1)) (f1 : ¬R x y (1,-1)) (f2 : ¬R x y (1,0))
    (r : R x y (2,-1)) : HasCycle x y 4 ∨ HasCycle x y 8 := by
  have clos : image x y (w5 (lastIdx 4)) = image x y (w5 ⟨0,by decide⟩) := by
    change image x y (-2,1) = image x y (0:P)
    rw [image_zero]
    exact negR x y c (2,-1) r
  left
  refine chain (n:=4) (by decide) (by decide) x y c w5 w5diff (by decide) (by decide) clos ?_
  intro p hp
  simp [w5diff] at hp
  rcases hp with rfl | rfl
  · exact f1
  · exact f2
def w6 : Fin 5 → P := fun i => (#[(0,0), (0,0), (-1,0), (-1,0), (-2,0)] : Array P)[i.val]!
def w6diff : List P := [(1,0)]
theorem w6case (f0 : ¬R x y (0,1)) (f1 : ¬R x y (1,-1)) (f2 : ¬R x y (1,0))
    (r : R x y (2,0)) : HasCycle x y 4 ∨ HasCycle x y 8 := by
  have clos : image x y (w6 (lastIdx 4)) = image x y (w6 ⟨0,by decide⟩) := by
    change image x y (-2,0) = image x y (0:P)
    rw [image_zero]
    exact negR x y c (2,0) r
  left
  refine chain (n:=4) (by decide) (by decide) x y c w6 w6diff (by decide) (by decide) clos ?_
  intro p hp
  simp [w6diff] at hp
  rcases hp with rfl
  · exact f2
def w3 : Fin 9 → P := fun i => (#[(0,0), (0,0), (-1,0), (-1,0), (-2,0), (-2,0), (-2,-1), (-1,-1), (-1,-2)] : Array P)[i.val]!
def w3diff : List P := [(0,1), (1,-1), (1,0), (1,1), (2,0), (2,1)]
theorem w3case (f0 : ¬R x y (0,1)) (f1 : ¬R x y (1,-1)) (f2 : ¬R x y (1,0))
    (r : R x y (1,2)) : HasCycle x y 4 ∨ HasCycle x y 8 := by
  have clos : image x y (w3 (lastIdx 8)) = image x y (w3 ⟨0,by decide⟩) := by
    change image x y (-1,-2) = image x y (0:P)
    rw [image_zero]
    exact negR x y c (1,2) r
  by_cases bad : ∃ q ∈ w3diff, R x y q
  · obtain ⟨q,hq,he⟩ := bad
    simp [w3diff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (f0 he)
    · exact False.elim (f1 he)
    · exact False.elim (f2 he)
    · have h := addR x y c ((1:ℤ) • ((1,2):P)) ((-1:ℤ) • ((1,1):P)) (zR x y c _ r 1) (zR x y c _ he (-1))
      have eq : ((1:ℤ) • ((1,2):P)) + ((-1:ℤ) • ((1,1):P)) = (0,1) := by decide
      rw [eq] at h
      exact False.elim (f0 h)
    · have h := addR x y c ((-1:ℤ) • ((1,2):P)) ((1:ℤ) • ((2,0):P)) (zR x y c _ r (-1)) (zR x y c _ he 1)
      have eq : ((-1:ℤ) • ((1,2):P)) + ((1:ℤ) • ((2,0):P)) = (1,-2) := by decide
      rw [eq] at h
      exact w1case x y c f0 f1 f2 h
    · have h := addR x y c ((-1:ℤ) • ((1,2):P)) ((1:ℤ) • ((2,1):P)) (zR x y c _ r (-1)) (zR x y c _ he 1)
      have eq : ((-1:ℤ) • ((1,2):P)) + ((1:ℤ) • ((2,1):P)) = (1,-1) := by decide
      rw [eq] at h
      exact False.elim (f1 h)
  · right
    exact chain (n:=8) (by decide) (by decide) x y c w3 w3diff (by decide) (by decide) clos (fun q hq hr => bad ⟨q,hq,hr⟩)
def w7 : Fin 9 → P := fun i => (#[(0,0), (0,0), (-1,0), (-1,1), (-2,1), (-2,1), (-2,0), (-2,0), (-2,-1)] : Array P)[i.val]!
def w7diff : List P := [(0,1), (1,-1), (1,0), (1,1), (2,-1), (2,0)]
theorem w7case (f0 : ¬R x y (0,1)) (f1 : ¬R x y (1,-1)) (f2 : ¬R x y (1,0))
    (r : R x y (2,1)) : HasCycle x y 4 ∨ HasCycle x y 8 := by
  have clos : image x y (w7 (lastIdx 8)) = image x y (w7 ⟨0,by decide⟩) := by
    change image x y (-2,-1) = image x y (0:P)
    rw [image_zero]
    exact negR x y c (2,1) r
  by_cases bad : ∃ q ∈ w7diff, R x y q
  · obtain ⟨q,hq,he⟩ := bad
    simp [w7diff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (f0 he)
    · exact False.elim (f1 he)
    · have h := addR x y c ((1:ℤ) • ((2,1):P)) ((-2:ℤ) • ((1,0):P)) (zR x y c _ r 1) (zR x y c _ he (-2))
      have eq : ((1:ℤ) • ((2,1):P)) + ((-2:ℤ) • ((1,0):P)) = (0,1) := by decide
      rw [eq] at h
      exact False.elim (f0 h)
    · have h := addR x y c ((-1:ℤ) • ((2,1):P)) ((2:ℤ) • ((1,1):P)) (zR x y c _ r (-1)) (zR x y c _ he 2)
      have eq : ((-1:ℤ) • ((2,1):P)) + ((2:ℤ) • ((1,1):P)) = (0,1) := by decide
      rw [eq] at h
      exact False.elim (f0 h)
    · have h := addR x y c ((1:ℤ) • ((2,1):P)) ((-1:ℤ) • ((2,-1):P)) (zR x y c _ r 1) (zR x y c _ he (-1))
      have eq : ((1:ℤ) • ((2,1):P)) + ((-1:ℤ) • ((2,-1):P)) = (0,2) := by decide
      rw [eq] at h
      exact w0case x y c f0 f1 f2 h
    · have h := addR x y c ((1:ℤ) • ((2,1):P)) ((-1:ℤ) • ((2,0):P)) (zR x y c _ r 1) (zR x y c _ he (-1))
      have eq : ((1:ℤ) • ((2,1):P)) + ((-1:ℤ) • ((2,0):P)) = (0,1) := by decide
      rw [eq] at h
      exact False.elim (f0 h)
  · right
    exact chain (n:=8) (by decide) (by decide) x y c w7 w7diff (by decide) (by decide) clos (fun q hq hr => bad ⟨q,hq,hr⟩)
def w8 : Fin 9 → P := fun i => (#[(0,0), (0,0), (-1,0), (-1,1), (-2,1), (-2,2), (-3,2), (-3,2), (-3,1)] : Array P)[i.val]!
def w8diff : List P := [(1,-1), (1,0), (2,-2), (2,-1), (3,-2)]
theorem w8case (f0 : ¬R x y (0,1)) (f1 : ¬R x y (1,-1)) (f2 : ¬R x y (1,0))
    (r : R x y (3,-1)) : HasCycle x y 4 ∨ HasCycle x y 8 := by
  have clos : image x y (w8 (lastIdx 8)) = image x y (w8 ⟨0,by decide⟩) := by
    change image x y (-3,1) = image x y (0:P)
    rw [image_zero]
    exact negR x y c (3,-1) r
  by_cases bad : ∃ q ∈ w8diff, R x y q
  · obtain ⟨q,hq,he⟩ := bad
    simp [w8diff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (f1 he)
    · have h := addR x y c ((-1:ℤ) • ((3,-1):P)) ((3:ℤ) • ((1,0):P)) (zR x y c _ r (-1)) (zR x y c _ he 3)
      have eq : ((-1:ℤ) • ((3,-1):P)) + ((3:ℤ) • ((1,0):P)) = (0,1) := by decide
      rw [eq] at h
      exact False.elim (f0 h)
    · have h := addR x y c ((1:ℤ) • ((3,-1):P)) ((-1:ℤ) • ((2,-2):P)) (zR x y c _ r 1) (zR x y c _ he (-1))
      have eq : ((1:ℤ) • ((3,-1):P)) + ((-1:ℤ) • ((2,-2):P)) = (1,1) := by decide
      rw [eq] at h
      exact w2case x y c f0 f1 f2 h
    · have h := addR x y c ((2:ℤ) • ((3,-1):P)) ((-3:ℤ) • ((2,-1):P)) (zR x y c _ r 2) (zR x y c _ he (-3))
      have eq : ((2:ℤ) • ((3,-1):P)) + ((-3:ℤ) • ((2,-1):P)) = (0,1) := by decide
      rw [eq] at h
      exact False.elim (f0 h)
    · have h := addR x y c ((1:ℤ) • ((3,-1):P)) ((-1:ℤ) • ((3,-2):P)) (zR x y c _ r 1) (zR x y c _ he (-1))
      have eq : ((1:ℤ) • ((3,-1):P)) + ((-1:ℤ) • ((3,-2):P)) = (0,1) := by decide
      rw [eq] at h
      exact False.elim (f0 h)
  · right
    exact chain (n:=8) (by decide) (by decide) x y c w8 w8diff (by decide) (by decide) clos (fun q hq hr => bad ⟨q,hq,hr⟩)
def w9 : Fin 9 → P := fun i => (#[(0,0), (0,0), (-1,0), (-1,0), (-2,0), (-2,1), (-3,1), (-3,1), (-3,0)] : Array P)[i.val]!
def w9diff : List P := [(1,-1), (1,0), (2,-1), (2,0), (3,-1)]
theorem w9case (f0 : ¬R x y (0,1)) (f1 : ¬R x y (1,-1)) (f2 : ¬R x y (1,0))
    (r : R x y (3,0)) : HasCycle x y 4 ∨ HasCycle x y 8 := by
  have clos : image x y (w9 (lastIdx 8)) = image x y (w9 ⟨0,by decide⟩) := by
    change image x y (-3,0) = image x y (0:P)
    rw [image_zero]
    exact negR x y c (3,0) r
  by_cases bad : ∃ q ∈ w9diff, R x y q
  · obtain ⟨q,hq,he⟩ := bad
    simp [w9diff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (f1 he)
    · exact False.elim (f2 he)
    · have h := addR x y c ((-1:ℤ) • ((3,0):P)) ((2:ℤ) • ((2,-1):P)) (zR x y c _ r (-1)) (zR x y c _ he 2)
      have eq : ((-1:ℤ) • ((3,0):P)) + ((2:ℤ) • ((2,-1):P)) = (1,-2) := by decide
      rw [eq] at h
      exact w1case x y c f0 f1 f2 h
    · have h := addR x y c ((1:ℤ) • ((3,0):P)) ((-1:ℤ) • ((2,0):P)) (zR x y c _ r 1) (zR x y c _ he (-1))
      have eq : ((1:ℤ) • ((3,0):P)) + ((-1:ℤ) • ((2,0):P)) = (1,0) := by decide
      rw [eq] at h
      exact False.elim (f2 h)
    · have h := addR x y c ((1:ℤ) • ((3,0):P)) ((-1:ℤ) • ((3,-1):P)) (zR x y c _ r 1) (zR x y c _ he (-1))
      have eq : ((1:ℤ) • ((3,0):P)) + ((-1:ℤ) • ((3,-1):P)) = (0,1) := by decide
      rw [eq] at h
      exact False.elim (f0 h)
  · right
    exact chain (n:=8) (by decide) (by decide) x y c w9 w9diff (by decide) (by decide) clos (fun q hq hr => bad ⟨q,hq,hr⟩)
def origin : Fin 17 → P := fun i => (#[(0,0), (0,0), (-1,0), (-1,0), (-2,0), (-2,0), (-3,0), (-3,1), (-3,1), (-2,1), (-2,1), (-2,2), (-2,2), (-1,2), (-1,1), (0,1), (0,0)] : Array P)[i.val]!
def originDiff : List P := [(0,1), (0,2), (1,-2), (1,-1), (1,0), (1,1), (1,2), (2,-2), (2,-1), (2,0), (2,1), (3,-1), (3,0)]
theorem commute_case (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    HasCycle x y 4 ∨ HasCycle x y 8 ∨ HasCycle x y 16 := by
  have f0 : ¬R x y (0,1) := by simpa [R,image] using hy
  have f1 : ¬R x y (1,-1) := by simpa [R,image] using (show ¬ y⁻¹*x=1 from by intro h; apply hxy; have e := congrArg (y*·) h; simpa [mul_assoc] using e)
  have f2 : ¬R x y (1,0) := by simpa [R,image] using hx
  by_cases bad : ∃ d∈originDiff, R x y d
  · obtain ⟨d,hd,hr⟩ := bad
    simp [originDiff] at hd
    have q : HasCycle x y 4 ∨ HasCycle x y 8 := by
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact False.elim (f0 hr)
      · exact w0case x y c f0 f1 f2 hr
      · exact w1case x y c f0 f1 f2 hr
      · exact False.elim (f1 hr)
      · exact False.elim (f2 hr)
      · exact w2case x y c f0 f1 f2 hr
      · exact w3case x y c f0 f1 f2 hr
      · exact w4case x y c f0 f1 f2 hr
      · exact w5case x y c f0 f1 f2 hr
      · exact w6case x y c f0 f1 f2 hr
      · exact w7case x y c f0 f1 f2 hr
      · exact w8case x y c f0 f1 f2 hr
      · exact w9case x y c f0 f1 f2 hr
    exact q.elim Or.inl (fun h => Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (chain (n:=16) (by decide) (by decide) x y c origin originDiff (by decide) (by decide) rfl (fun d hd hr => bad ⟨d,hd,hr⟩)))

end HaarAbel

#print axioms HaarAbel.commute_case
