import Physical
import Mathlib.Data.Prod.Lex

namespace PackingSeparator

abbrev Stamp := ℕ ×ₗ ℕ

def tag1 (K : ℕ) (flip : Bool) : ℕ := if flip then K else 0
def tag3 (K : ℕ) (flip : Bool) : ℕ := if flip then 0 else K

def anchorStamp (t r : ℕ) : Stamp := toLex (2*t+1+r,0)

/-- Local score. In the potentially competing two private chains, the flip
chooses which chain is earlier. Every comparison in a source window remains strict. -/
def localStamp (K a b c t : ℕ) (flip : Bool) (u : ℕ) : Stamp :=
  if u=0 then anchorStamp t 0
  else if u<a then toLex (2*t+1,tag1 K flip+u)
  else if u=a then anchorStamp t 1
  else if u<b then toLex (2*t+2,u)
  else if u=b then anchorStamp (t+1) 0
  else if u<c then toLex (2*t+3,tag3 K flip+u)
  else if u=c then anchorStamp (t+1) 1
  else toLex (2*t+4,u)

set_option maxHeartbeats 3000000 in
lemma localStamp_lt {K a b c : ℕ} (ha : 0<a) (hb : a<b) (hc : b<c)
    (t : ℕ) (flip : Bool) {u v : ℕ} (h : u<v) :
    localStamp K a b c t flip u < localStamp K a b c t flip v := by
  unfold localStamp
  split_ifs <;> simp only [anchorStamp,Prod.Lex.toLex_lt_toLex'] <;> omega

variable {K J : ℕ} (hk : 4≤K) (p : Equiv.Perm (Fin K))
variable {a b c : ℕ}

def stamp (K J : ℕ) (_hk : 4≤K) (p : Equiv.Perm (Fin K)) (a b c : ℕ)
    (flip : Bool) (v : Fin (nPos K J)) : Stamp :=
  let r := v.val%(K-2)
  let t := v.val/(K-2)
  if h : r < K then
    if r<2 then anchorStamp t r
    else localStamp K a b c t flip (p ⟨r,h⟩).val
  else toLex (0,0)

lemma on_block (t : Fin (J+1)) (i : Fin 2) (flip : Bool) :
    stamp K J hk p a b c flip (atBlock (K:=K) t i) = anchorStamp t.val i.val := by
  have H := block_parts hk t i
  unfold stamp
  dsimp only
  rw [H.1,H.2]
  have hi := i.isLt
  rw [dite_eq_left (show i.val<K by omega),ite_eq_left hi]

lemma on_private (t : Fin J) {i : Fin K} (hi : i.val<K-2) (q : 2 ≤ i.val) (flip : Bool) :
    stamp K J hk p a b c flip (atPos hk t i) = localStamp K a b c t.val flip (p i).val := by
  have H := window_private_parts hk t hi
  unfold stamp
  dsimp only
  rw [H.1,H.2,dite_eq_left i.isLt,ite_eq_right (not_lt_of_ge q)]

lemma on_window (ha : 0<a) (hb : a<b) (hc : b<c)
    (r0 : (p ⟨0,by omega⟩).val=0) (r1 : (p ⟨1,by omega⟩).val=a)
    (r2 : (p ⟨K-2,by omega⟩).val=b) (r3 : (p ⟨K-1,by omega⟩).val=c)
    (t : Fin J) (i : Fin K) (flip : Bool) :
    stamp K J hk p a b c flip (atPos hk t i) =
      localStamp K a b c t.val flip (p i).val := by
  have hi := i.isLt
  by_cases H0 : i.val=0
  · have E : i=(⟨0,by omega⟩ : Fin K) := Fin.ext H0
    rw [E]
    have G : atPos hk t ⟨0,by omega⟩=atBlock (K:=K) t.castSucc 0 := prefix_pos hk t (0 : Fin 2)
    rw [G,on_block,r0]
    simp [localStamp]
  by_cases H1 : i.val=1
  · have E : i=(⟨1,by omega⟩ : Fin K) := Fin.ext H1
    rw [E]
    have G : atPos hk t ⟨1,by omega⟩=atBlock (K:=K) t.castSucc 1 := prefix_pos hk t (1 : Fin 2)
    rw [G,on_block,r1]
    simp [localStamp,show a≠0 by omega]
  by_cases H2 : i.val=K-2
  · have E : i=(⟨K-2,by omega⟩ : Fin K) := Fin.ext H2
    rw [E]
    have F := suffix_pos hk t (0 : Fin 2)
    have G : atPos hk t ⟨K-2,by omega⟩=atBlock (K:=K) t.succ 0 := F
    rw [G,on_block,r2]
    simp [localStamp,show b≠0 by omega,show ¬b<a by omega,show b≠a by omega]
  by_cases H3 : i.val=K-1
  · have E : i=(⟨K-1,by omega⟩ : Fin K) := Fin.ext H3
    rw [E]
    have G : atPos hk t ⟨K-1,by omega⟩=atBlock (K:=K) t.succ 1 := by
      have F := suffix_pos hk t (1 : Fin 2)
      have I : (⟨K-2+(1:Fin 2).val,by omega⟩ : Fin K)=⟨K-1,by omega⟩ :=
        Fin.ext (by change K-2+1=K-1;omega)
      rwa [I] at F
    rw [G,on_block,r3]
    simp [localStamp,show c≠0 by omega,show ¬c<a by omega,show c≠a by omega,
      show ¬c<b by omega,show c≠b by omega]
  exact on_private hk p t (by omega) (by omega) flip

lemma stamp_edges (ha : 0<a) (hb : a<b) (hc : b<c)
    (r0 : (p ⟨0,by omega⟩).val=0) (r1 : (p ⟨1,by omega⟩).val=a)
    (r2 : (p ⟨K-2,by omega⟩).val=b) (r3 : (p ⟨K-1,by omega⟩).val=c)
    (flip : Bool) :
    ∀ x y : Fin (nPos K J), stepEdges hk p x y →
      stamp K J hk p a b c flip x < stamp K J hk p a b c flip y := by
  intro x y H
  obtain ⟨t,i,l,rfl,rfl,q⟩ := H
  rw [on_window hk p ha hb hc r0 r1 r2 r3,on_window hk p ha hb hc r0 r1 r2 r3]
  exact localStamp_lt ha hb hc t.val flip q

end PackingSeparator
