import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace HaarOwnerCertificate

def Covered (shards : List (List ℕ)) (owner : ℕ → ℕ × ℕ) (offset : ℕ) : Prop :=
  ∀ (s i a : ℕ) (l : List ℕ), shards[s]? = some l → l[i]? = some a →
    owner a = (offset+s,i)

theorem position_unique (shards : List (List ℕ)) (owner : ℕ → ℕ × ℕ) (offset : ℕ)
    (hc : Covered shards owner offset)
    {s t i j a : ℕ} {l m : List ℕ} (hs : shards[s]? = some l) (ht : shards[t]? = some m)
    (hi : l[i]? = some a) (hj : m[j]? = some a) : s=t ∧ i=j := by
  have eq := (hc s i a l hs hi).symm.trans (hc t j a m ht hj)
  have first := congrArg Prod.fst eq
  exact ⟨by dsimp at first; omega,congrArg Prod.snd eq⟩

theorem nodup_flatten (shards : List (List ℕ)) (owner : ℕ → ℕ × ℕ) (offset : ℕ)
    (hc : Covered shards owner offset) : shards.flatten.Nodup := by
  induction shards generalizing offset with
  | nil => simp
  | cons head tail ih =>
    have tail_cov : Covered tail owner (offset+1) := by
      intro s i a l hs hi
      simpa [Nat.add_assoc,Nat.add_comm 1 s] using hc (s+1) i a l (by simpa using hs) hi
    have hd : head.Nodup := by
      apply List.nodup_iff_injective_get.mpr
      intro i j e
      apply Fin.ext
      have hi : head[i.val]?=some (head.get i) := List.getElem?_eq_getElem i.isLt
      have hj : head[j.val]?=some (head.get i) := by rw [e]; exact List.getElem?_eq_getElem j.isLt
      exact (position_unique _ owner offset hc (s:=0) (t:=0) (by simp) (by simp) hi hj).2
    have disj : head.Disjoint tail.flatten := by
      rw [List.disjoint_left]
      intro a ha hb
      obtain ⟨m,hm,ha'⟩ := List.mem_flatten.mp hb
      obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp ha
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp ha'
      obtain ⟨s,hs⟩ := List.mem_iff_getElem?.mp hm
      have ht : (head::tail)[s+1]?=some m := by simpa using hs
      have q := (position_unique _ owner offset hc (s:=0) (by simp) ht hi hj).1
      omega
    exact hd.append (ih _ tail_cov) disj

def checkShard (owner : ℕ → ℕ × ℕ) (s : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, a::keys => decide (owner a=(s,i)) && checkShard owner s (i+1) keys

theorem checkShard_sound (owner : ℕ → ℕ × ℕ) (s k : ℕ) (keys : List ℕ)
    (h : checkShard owner s k keys=true) :
    ∀ i a, keys[i]?=some a → owner a=(s,k+i) := by
  induction keys generalizing k with
  | nil => simp
  | cons a keys ih =>
    simp only [checkShard,Bool.and_eq_true,decide_eq_true_eq] at h
    intro i b he
    cases i with
    | zero =>
      simp at he
      simpa [he] using h.1
    | succ i =>
      simpa [Nat.add_assoc,Nat.add_comm 1 i] using ih (k+1) h.2 i b (by simpa using he)

theorem of_checks (shards : List (List ℕ)) (owner : ℕ → ℕ × ℕ)
    (checks : ∀ s l, shards[s]?=some l → checkShard owner s 0 l=true) :
    shards.flatten.Nodup := by
  apply nodup_flatten shards owner 0
  intro s i a l hs hi
  simpa using checkShard_sound owner s 0 l (checks s l hs) i a hi

theorem checkShard_append (owner : ℕ → ℕ × ℕ) (s k : ℕ) (a b : List ℕ) :
    checkShard owner s k (a++b) =
      (checkShard owner s k a && checkShard owner s (k+a.length) b) := by
  induction a generalizing k with
  | nil => simp [checkShard]
  | cons t a ih =>
    simp only [List.cons_append,checkShard,List.length_cons,ih,Bool.and_assoc]
    rw [show k+1+a.length=k+(a.length+1) by omega]

theorem checkShard_join (owner : ℕ → ℕ × ℕ) (s k : ℕ) (a b : List ℕ)
    (ha : checkShard owner s k a=true)
    (hb : checkShard owner s (k+a.length) b=true) :
    checkShard owner s k (a++b)=true := by rw [checkShard_append,ha,hb]; rfl

end HaarOwnerCertificate
#print axioms HaarOwnerCertificate.of_checks
