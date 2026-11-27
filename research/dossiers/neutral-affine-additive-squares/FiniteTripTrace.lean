import FiniteTripStep
import NeutralTrace

namespace FiniteTripTrace
open FiniteTrip FiniteTripStep TripTrace CutOrder AffineAddress PhaseProduct
variable (D : Finset ℤ) (f : ℤ → List ℤ)
variable (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)
variable (A : (ℤ×ℤ) →+ (ℤ×ℤ))
variable (aff : ∀ x ∈ D, σ (f x)=A (σ [x]))

include aff in
theorem sig_list (xs : List ℤ) (hx : ∀ z ∈ xs, z ∈ D) :
    σ (xs.flatMap f) = A (σ xs) := by
  induction xs with
  | nil => exact (map_zero A).symm
  | cons x t ih =>
    have h₁ := aff x (hx x (by simp))
    have h₂ := ih (fun z hz => hx z (by simp [hz]))
    rw [List.flatMap_cons,sig_append,h₁,h₂,← map_add,← sig_append]
    rfl

include aff in
theorem delta_local {w : List ℤ} (T : Triple w) (p : Offset f T)
    (hw : ∀ z ∈ w, z ∈ D) :
    delta (desc f T p) = A (delta T) +
      (σ p.a.head + σ p.c.head - (σ p.b.head + σ p.b.head)) := by
  have hs (X : CutLift.Cut w) : ∀ z ∈ X.head, z ∈ D := by
    intro z hz
    exact hw z ((congrArg (fun l : List ℤ => z ∈ l) X.decomp).mpr (by simp [hz]))
  simp only [delta,desc,CutLift.lift,sig_append,sig_list D f A aff _ (hs T.a),
    sig_list D f A aff _ (hs T.b),sig_list D f A aff _ (hs T.c)]
  exact diff_step _ _ _ _ _ _ _

def machine (u v : ℤ×ℤ) (m : ℤ) (neg : Bool) : Machine (State D) (Edge D f) :=
  ⟨src D f, dst D f closed,
    fun i => NeutralTrace.pro v (stamp D f i),
    fun i => NeutralTrace.pro u (stamp D f i),m,neg⟩

variable (u v : ℤ×ℤ) (m : ℤ) (neg : Bool)

include closed in
theorem iterMem (a : ℤ) (ha : a∈D) (n : ℕ) : ∀ z ∈ iter f a n, z∈D := by
  induction n with
  | zero =>
    intro z hz
    have he : z=a := by simpa [iter] using hz
    simpa [he] using ha
  | succ n ih => exact child_mem D f closed ih

def vertex (a : ℤ) (ha : a∈D) {n : ℕ} (T : Triple (iter f a n)) :=
  restrictShape D T (iterMem D f closed a ha n)

include aff in
theorem realizes (a : ℤ) (ha : a∈D) {n : ℕ} (T : Triple (iter f a n))
    (ho : ordered T) {x y : State D} {L : List (Edge D f)}
    (h : Path (machine D f closed u v m neg) x y L)
    (hx : x = vertex D f closed a ha T) :
    ∃ (r : ℕ) (U : Triple (iter f a r)), ordered U ∧
      y = vertex D f closed a ha U ∧
      delta U = NeutralTrace.run A (delta T) (L.map (stamp D f)) := by
  induction h generalizing n with
  | nil x => exact ⟨n,T,ho,hx,rfl⟩
  | @cons e y L h ih =>
    obtain ⟨p,hp,ht,hs⟩ := step_matches D f closed T (iterMem D f closed _ ha _) ho e hx
    have df : delta (desc f T p) = NeutralTrace.plus (A (delta T)) (stamp D f e) := by
      rw [delta_local D f A aff T p (iterMem D f closed a ha n),hs]
      rfl
    obtain ⟨r,U,hU,hv,hd⟩ := ih (n:=n+1) (desc f T p) hp ht
    refine ⟨r,U,hU,hv,?_⟩
    exact hd.trans (congrArg (fun x => NeutralTrace.run A x (L.map (stamp D f))) df)

theorem path_append {x y z : State D} {L R : List (Edge D f)}
    (h : Path (machine D f closed u v m neg) x y L)
    (j : Path (machine D f closed u v m neg) y z R) :
    Path (machine D f closed u v m neg) x z (L++R) := by
  induction h with
  | nil => exact j
  | cons e l ih => exact .cons e (ih j)

theorem run_append (p : ℤ×ℤ) (L R : List (ℤ×ℤ)) :
    NeutralTrace.run A p (L++R) = NeutralTrace.run A (NeutralTrace.run A p L) R := by
  induction L generalizing p with
  | nil => rfl
  | cons c L ih => exact ih _

theorem root_ordered (a : ℤ) : ordered (root a) := ⟨le_rfl,le_rfl⟩
theorem root_zero (a : ℤ) : delta (root a)=0 := rfl

include aff in
theorem from_triple (a : ℤ) (ha : a∈D) {n : ℕ} (T : Triple (iter f a n))
    (ho : ordered T) :
    ∃ L, Path (machine D f closed u v m neg) (vertex D f closed a ha (n:=0) (root a))
      (vertex D f closed a ha T) L ∧
      delta T = NeutralTrace.run A 0 (L.map (stamp D f)) := by
  induction n with
  | zero =>
    have h := every_representable f a 0 T
    cases h
    exact ⟨[],.nil _,root_zero _⟩
  | succ n ih =>
    obtain ⟨X,p,e⟩ := exists_ancestor f T
    subst T
    have op := parent_ordered f X p ho
    obtain ⟨L,hL,hΔ⟩ := ih X op
    obtain ⟨i,hi,hj,hk⟩ := step_exists D f closed X (iterMem D f closed _ ha _) op p ho
    have H : Path (machine D f closed u v m neg) (vertex D f closed a ha X)
        (vertex D f closed a ha (n:=n+1) (desc f X p)) [i] := by
      have h : Path (machine D f closed u v m neg)
          (src D f i) (dst D f closed i) [i] := .cons i (.nil _)
      rw [hi,hj] at h
      exact h
    refine ⟨L++[i], path_append D f closed u v m neg hL H,?_⟩
    rw [List.map_append,run_append A,← hΔ]
    exact (delta_local D f A aff X p (iterMem D f closed a ha n)).trans (by
      simp only [List.map_cons,List.map_nil,NeutralTrace.run,hk]
      rfl)

end FiniteTripTrace

#print axioms FiniteTripTrace.realizes
#print axioms FiniteTripTrace.from_triple
