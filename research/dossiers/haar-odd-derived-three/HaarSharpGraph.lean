import HaarSharpCore

namespace HaarSharpGraph
open HaarCycle HaarAllNoncommuting HaarSharpCore

theorem branch (p q : Bool × H) (e : haarAdj x y p q) :
    q.1 = !p.1 ∧ ∃ c : Fin 3,
      q.2 = p.2 * (if p.1 then (port c)⁻¹ else port c) := by
  cases h : p.1
  · simp [haarAdj,h] at e
    rcases e with ⟨a,b|b|b⟩
    · exact ⟨by simp [a],0,by simp [port,h,b]⟩
    · exact ⟨by simp [a],1,by simpa [port,h] using b⟩
    · exact ⟨by simp [a],2,by simpa [port,h] using b⟩
  · simp [haarAdj,h] at e
    rcases e with ⟨a,b|b|b⟩
    · exact ⟨by simp [a],0,by simp [port,h,b]⟩
    · exact ⟨by simp [a],1,by simpa [port,h] using (eq_mul_inv_iff_mul_eq.mpr b.symm)⟩
    · exact ⟨by simp [a],2,by simpa [port,h] using (eq_mul_inv_iff_mul_eq.mpr b.symm)⟩

def segment (c : ℕ → Fin 3) (j : ℕ) : ℕ → List (Fin 3)
  | 0 => []
  | n+1 => c j :: segment c (j+1) n

theorem segment_len (c : ℕ → Fin 3) (j n : ℕ) :
    (segment c j n).length=n := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp [segment,ih]

theorem segment_good (c : ℕ → Fin 3) (j n : ℕ)
    (hh : ∀ k < n-1, c (j+k)≠c (j+k+1)) : good (segment c j n) = true := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have h1 := hh 0 (by omega)
      have h2 := ih (j+1) (fun k hk => by
        simpa only [Nat.add_assoc,Nat.add_comm 1 k] using hh (k+1) (by omega))
      change (c j != c (j+1) && good (c (j+1)::segment c (j+2) n))=true
      have hj : c j≠c (j+1) := by simpa using h1
      simp [hj,show good (c (j+1)::segment c (j+2) n) = true from h2]

theorem segment_product (g : ℕ → H) (c : ℕ → Fin 3) (bias j n : ℕ)
    (hh : ∀ k<n, g (j+k+1)=g (j+k)*signPort (bias+(j+k)) (c (j+k))) :
    g (j+n)=g j*prodFrom (bias+j) (segment c j n) := by
  induction n generalizing j with
  | zero => simp [segment,prodFrom]
  | succ n ih =>
    have h1 := hh 0 (by omega)
    have h2 := ih (j+1) (fun k hk => by
      simpa only [Nat.add_assoc,Nat.add_comm 1 k] using hh (k+1) (by omega))
    rw [show j+(n+1)=(j+1)+n by omega,h2]
    simp only [segment,prodFrom,← mul_assoc]
    have he : bias+(j+1)=bias+j+1 := by omega
    rw [he, ← show g (j+1)=g j*signPort (bias+j) (c j) by simpa using h1]

theorem no_cycle (n : ℕ) (hn : n=4 ∨ n=6 ∨ n=8) : ¬ HaarAllNoncommuting.HasCycle x y n := by
  rintro ⟨v,hv,adj⟩
  have nz : 0<n := by rcases hn with h|h|h <;> omega
  let point (i : ℕ) : Fin n := ⟨i%n,Nat.mod_lt _ nz⟩
  let a (i : ℕ) : Bool×H := v (point i)
  have step (i : ℕ) : haarAdj x y (a i) (a (i+1)) := by
    have h : (⟨((point i).val+1)%n,Nat.mod_lt _ nz⟩ : Fin n) = point (i+1) := by
      apply Fin.ext
      change (i%n+1)%n=(i+1)%n
      simpa only [Nat.mod_eq_of_lt (show 1<n by rcases hn with r|r|r <;> omega)] using (Nat.add_mod i 1 n).symm
    have t : haarAdj x y (v (point i))
        (v ⟨((point i).val+1)%n,Nat.mod_lt _ nz⟩) := adj (point i)
    rw [h] at t
    exact t
  have hs (i : ℕ) := (branch _ _ (step i)).1
  let c (i : ℕ) := Classical.choose (branch _ _ (step i)).2
  have hc (i : ℕ) : (a (i+1)).2 =
      (a i).2*(if (a i).1 then (port (c i))⁻¹ else port (c i)) :=
    Classical.choose_spec (branch _ _ (step i)).2
  have bounce (i : ℕ) (eq : c i=c (i+1)) : a (i+2)=a i := by
    apply Prod.ext
    · rw [show i+2=i+1+1 by omega,hs (i+1),hs i]; simp
    · rw [show i+2=i+1+1 by omega,hc (i+1),hc i,hs i,← eq]
      cases hh : (a i).1 <;> simp [hh,mul_assoc]
  have goodAdj (i : ℕ) (hi : i<n-1) : c i ≠ c (i+1) := by
    intro eq
    have hh : (i+2)%n=i%n := congrArg Fin.val (hv (bounce i eq))
    rw [Nat.mod_eq_of_lt (show i<n by omega)] at hh
    by_cases g : i+2<n
    · rw [Nat.mod_eq_of_lt g] at hh; omega
    · have e : i+2=n := by omega
      rw [e,Nat.mod_self] at hh
      rcases hn with w|w|w <;> omega
  let b : ℕ := if (a 0).1 then 1 else 0
  have hb (i : ℕ) : (a i).1 = decide ((b+i)%2=1) := by
    induction i with
    | zero => cases z : (a 0).1 <;> simp [b,z]
    | succ i ih =>
      rw [hs i, ih]
      by_cases q : (b+i)%2=1
      · have r : (b+(i+1))%2≠1 := by omega
        simp [q,r]
      · have r : (b+(i+1))%2=1 := by omega
        simp [q,r]
  have hp (i : ℕ) : (a (i+1)).2 = (a i).2*signPort (b+i) (c i) := by
    rw [hc i,hb i]
    by_cases q : (b+i)%2=1
    · have r : (b+i)%2≠0 := by omega
      simp [signPort,q,r]
    · have r : (b+i)%2=0 := by omega
      simp [signPort,q,r]
  have endPt : a n=a 0 := by
    apply congrArg v
    apply Fin.ext
    simp [point]
  have prod := segment_product (fun i => (a i).2) c b 0 n (by simpa using fun i (_ : i<n) => hp i)
  rw [Nat.zero_add, endPt] at prod
  have he : prodFrom b (segment c 0 n)=1 := by
    apply mul_left_cancel (a:=(a 0).2)
    simpa using prod.symm
  have gg := segment_good c 0 n (by simpa using goodAdj)
  have len := segment_len c 0 n
  have invalid := no_word (segment c 0 n) (by rw [len]; exact hn) gg
  cases h : (a 0).1
  · have eq : b=0 := by simp [b,h]
    rw [eq] at he
    exact invalid.1 he
  · have eq : b=1 := by simp [b,h]
    rw [eq] at he
    exact invalid.2 he

theorem sharp : HaarAllNoncommuting.HasCycle x y 16 ∧
    ¬ HaarAllNoncommuting.HasCycle x y 4 ∧ ¬ HaarAllNoncommuting.HasCycle x y 8 := by
  have p := HaarBound16.sharpened x y z cx cy rel nz
  have n4 := no_cycle 4 (Or.inl rfl)
  have n8 := no_cycle 8 (Or.inr (Or.inr rfl))
  rcases p with h|h|h
  · exact False.elim (n4 h)
  · exact False.elim (n8 h)
  · exact ⟨h,n4,n8⟩

end HaarSharpGraph

#print axioms HaarSharpGraph.sharp
