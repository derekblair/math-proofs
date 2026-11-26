import HaarHalfCollision
import HaarMatrix31Packed

namespace HaarMatrix31WordsBridge

def ports : List (Fin 3) := [0,1,2]

theorem mem_ports (j : Fin 3) : j ∈ ports := by revert j; decide

def enumeration (last : ℕ) : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n+1 => ports.flatMap fun j => if j.val=last then [] else (enumeration j.val n).map (j::·)

def prefers (last : ℕ) : List (Fin 3) → Prop
  | [] => True
  | j::_ => j.val ≠ last

theorem can_enum (L : List (Fin 3)) (last : ℕ)
    (p : prefers last L) (g : HaarSharpCore.good L=true) :
    L ∈ enumeration last L.length := by
  induction L generalizing last with
  | nil => simp [enumeration]
  | cons j tail ih =>
    change j.val ≠ last at p
    have q : prefers j.val tail ∧ HaarSharpCore.good tail=true := by
      cases tail with
      | nil => exact ⟨trivial,rfl⟩
      | cons i t =>
        change ((j != i) && HaarSharpCore.good (i::t))=true at g
        have w : (j != i)=true ∧ HaarSharpCore.good (i::t)=true := by simpa only [Bool.and_eq_true] using g
        refine ⟨?_,w.2⟩
        intro e
        have e1 : j=i := Fin.ext e.symm
        simp [e1] at w
    simp only [List.length_cons,enumeration,List.mem_flatMap]
    exact ⟨j,mem_ports j,by simp [p,ih j.val q.1 q.2]⟩

theorem generated (L : List (Fin 3)) (n : ℕ) (len : L.length=n)
    (g : HaarSharpCore.good L=true) : L ∈ enumeration 3 n := by
  subst n
  apply can_enum _ _ _ g
  cases L with
  | nil => trivial
  | cons j t =>
    change j.val ≠ 3
    omega

def run {S : Type*} (step : Bool → Fin 3 → S → S) (a : S) (pos : Bool) :
    List (Fin 3) → S
  | [] => a
  | j::l => run step (step pos j a) (!pos) l

theorem map_keys (a : Array ℕ) (pos : Bool) (last n : ℕ) :
    (enumeration last n).map
      (fun L => HaarMatrix31Packed.key (run (fun p j s => HaarMatrix31Packed.move p j.val s) a pos L)) =
      HaarMatrix31Packed.words a pos last n := by
  induction n generalizing last a pos with
  | zero => rfl
  | succ n ih =>
    unfold enumeration HaarMatrix31Packed.words
    rw [List.map_flatMap]
    have H (j : Fin 3) :
        List.map (fun L => HaarMatrix31Packed.key
          (run (fun p j s => HaarMatrix31Packed.move p j.val s) a pos L))
          (if j.val = last then [] else List.map (j::·) (enumeration (↑j) n)) =
        if j.val=last then [] else HaarMatrix31Packed.words (HaarMatrix31Packed.move pos j.val a) (!pos) j.val n := by
      split
      · rfl
      · rw [List.map_map]
        exact ih _ _ _
    rw [show ([0,1,2] : List ℕ) = ports.map Fin.val by decide,List.flatMap_map]
    exact congrArg (fun f => ports.flatMap f) (funext H)

theorem nodup_map_inj {S T : Type*} (f : S → T) (L : List S)
    (nd : (L.map f).Nodup) {x y : S} (hx : x∈L) (hy : y∈L)
    (he : f x=f y) : x=y := by
  induction L with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.map_cons,List.nodup_cons] at nd
    rcases List.mem_cons.mp hx with h|h <;> rcases List.mem_cons.mp hy with j|j
    · exact h.trans j.symm
    · subst x
      exact False.elim (nd.1 (List.mem_map.mpr ⟨y,j,he.symm⟩))
    · subst y
      exact False.elim (nd.1 (List.mem_map.mpr ⟨x,h,he⟩))
    · exact ih nd.2 h j

theorem injective_keys (n : ℕ) (nd : (HaarMatrix31Packed.words HaarMatrix31Packed.zero true 3 n).Nodup)
    (L R : List (Fin 3)) (ll : L.length=n) (rl : R.length=n)
    (lg : HaarSharpCore.good L=true) (rg : HaarSharpCore.good R=true)
    (he : HaarMatrix31Packed.key (run (fun p j s => HaarMatrix31Packed.move p j.val s)
         HaarMatrix31Packed.zero true L) =
       HaarMatrix31Packed.key (run (fun p j s => HaarMatrix31Packed.move p j.val s)
         HaarMatrix31Packed.zero true R)) : L=R := by
  refine nodup_map_inj (fun L => HaarMatrix31Packed.key (run (fun p j s => HaarMatrix31Packed.move p j.val s) HaarMatrix31Packed.zero true L)) (enumeration 3 n) ?_ (generated _ _ ll lg) (generated _ _ rl rg) he
  rwa [map_keys]

theorem run_natural {S T : Type*} (stepS : Bool → Fin 3 → S → S)
    (stepT : Bool → Fin 3 → T → T) (project : S → T)
    (h : ∀ p j s, project (stepS p j s)=stepT p j (project s))
    (a : S) (pos : Bool) (L : List (Fin 3)) :
    project (run stepS a pos L) = run stepT (project a) pos L := by
  induction L generalizing a pos with
  | nil => rfl
  | cons j L ih =>
    simp only [run,ih,h]

theorem run_signed_mul {G : Type*} [Group G] (x y a : G) (bias : ℕ) (L : List (Fin 3)) :
    run (fun p j s => s * (if p then HaarHalfCollision.port x y j else
      (HaarHalfCollision.port x y j)⁻¹)) a (decide (bias%2=0)) L =
      a * HaarHalfCollision.prodFrom x y bias L := by
  induction L generalizing a bias with
  | nil => simp [run,HaarHalfCollision.prodFrom]
  | cons j t ih =>
    have h : (!(decide (bias%2=0)))=decide ((bias+1)%2=0) := by
      by_cases he : bias%2=0
      · have ne : (bias+1)%2≠0 := by omega
        simp [he,ne]
      · have eq : (bias+1)%2=0 := by omega
        simp [he,eq]
    rw [run,h,ih,HaarHalfCollision.prodFrom,HaarHalfCollision.signPort,mul_assoc]
    by_cases q : bias%2=0 <;> simp [q]
end HaarMatrix31WordsBridge
#print axioms HaarMatrix31WordsBridge.injective_keys
