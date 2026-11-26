import RibbonD3InvertCore

namespace RibbonD3Field
open RibbonAffine (pl)
variable {K : Type*} [Field K]
set_option maxHeartbeats 0
set_option maxRecDepth 30000

def tinyCoeff : Fin 5 → Int := ![-3,-2,-1,1,2]
def tinyReceipt (c d e : Fin 5) : TriReceipt :=
  (#[default,default,default,default,default,⟨(0,0),[11],[⟨11,(8,1),.order false 1 0 5⟩]⟩,⟨(0,0),[],[]⟩,⟨(0,0),[13],[⟨13,(5,4),.order false 2 1 1⟩]⟩,⟨(0,0),[37],[⟨37,(13,21),.order false 2 2 1⟩]⟩,⟨(0,0),[7, 7],[⟨7,(3,3),.order false 1 1 1⟩]⟩,⟨(0,0),[7],[⟨7,(5,1),.order false 1 1 1⟩]⟩,⟨(1,0),[5],[⟨5,(2,3),.order false 2 0 1⟩]⟩,⟨(0,0),[13],[⟨13,(9,9),.order false 2 1 1⟩]⟩,⟨(0,0),[19],[⟨19,(13,4),.order false 1 2 1⟩]⟩,⟨(1,0),[11],[⟨11,(4,2),.order true 1 0 5⟩]⟩,⟨(0,0),[5],[⟨5,(3,4),.order false 2 0 1⟩]⟩,⟨(1,0),[],[]⟩,⟨(0,0),[],[]⟩,⟨(0,0),[7],[⟨7,(2,5),.order false 1 1 1⟩]⟩,⟨(1,0),[5],[⟨5,(3,4),.order false 2 0 1⟩]⟩,⟨(0,0),[5, 7],[⟨5,(1,1),.pivot⟩, ⟨7,(4,6),.order false 1 1 1⟩]⟩,⟨(0,0),[23],[⟨23,(7,6),.order false 1 0 11⟩]⟩,⟨(0,0),[11],[⟨11,(3,6),.order true 1 0 5⟩]⟩,⟨(0,0),[13],[⟨13,(8,6),.order false 2 1 1⟩]⟩,⟨(0,0),[5, 5],[⟨5,(1,1),.pivot⟩]⟩,⟨(0,0),[29],[⟨29,(16,22),.order true 2 0 7⟩]⟩,⟨(0,0),[11],[⟨11,(7,1),.order false 1 0 5⟩]⟩,⟨(0,0),[7],[⟨7,(5,3),.order false 1 1 1⟩]⟩,⟨(0,0),[43],[⟨43,(23,16),.order false 1 1 7⟩]⟩,⟨(0,0),[61],[⟨61,(32,11),.order false 2 1 5⟩]⟩,default,default,default,default,default,⟨(0,1),[],[]⟩,⟨(0,0),[5],[⟨5,(3,1),.order false 2 0 1⟩]⟩,⟨(0,0),[7],[⟨7,(4,4),.order false 1 1 1⟩]⟩,⟨(0,0),[11],[⟨11,(6,3),.order false 1 0 5⟩]⟩,⟨(0,0),[13],[⟨13,(7,8),.order false 2 1 1⟩]⟩,⟨(0,0),[5],[⟨5,(2,2),.order false 2 0 1⟩]⟩,⟨(0,1),[],[]⟩,⟨(0,0),[],[]⟩,⟨(0,1),[],[]⟩,⟨(0,0),[5],[⟨5,(2,2),.order false 2 0 1⟩]⟩,default,default,default,default,default,⟨(0,0),[11],[⟨11,(3,2),.order true 1 0 5⟩]⟩,⟨(1,0),[],[]⟩,⟨(0,0),[7],[⟨7,(3,1),.order false 1 1 1⟩]⟩,⟨(0,0),[5, 5],[⟨5,(3,3),.order false 2 0 1⟩]⟩,⟨(1,0),[17],[⟨17,(3,12),.order false 4 0 1⟩]⟩,⟨(0,1),[],[]⟩,⟨(0,0),[],[]⟩,⟨(0,0),[5],[⟨5,(2,1),.order false 2 0 1⟩]⟩,⟨(0,0),[13],[⟨13,(2,8),.order false 2 1 1⟩]⟩,⟨(0,0),[17],[⟨17,(2,5),.order false 4 0 1⟩]⟩,default,default,default,default,default,default,default,default,default,default,⟨(0,0),[11],[⟨11,(9,9),.bad⟩]⟩,⟨(0,0),[7],[⟨7,(5,5),.order false 1 1 1⟩]⟩,⟨(0,1),[],[]⟩,⟨(0,0),[5],[⟨5,(3,3),.order false 2 0 1⟩]⟩,⟨(0,2),[],[]⟩,⟨(0,0),[31],[⟨31,(28,17),.order false 1 1 5⟩]⟩,⟨(1,0),[11],[⟨11,(8,7),.order false 1 0 5⟩]⟩,⟨(0,0),[13],[⟨13,(10,8),.order false 2 1 1⟩]⟩,⟨(0,0),[5],[⟨5,(2,4),.order false 2 0 1⟩]⟩,⟨(1,0),[7],[⟨7,(4,5),.order false 1 1 1⟩]⟩,⟨(0,0),[13],[⟨13,(11,2),.order false 2 1 1⟩]⟩,⟨(0,2),[],[]⟩,⟨(0,0),[5],[⟨5,(3,2),.order false 2 0 1⟩]⟩,⟨(0,1),[],[]⟩,⟨(0,0),[7],[⟨7,(5,2),.order false 1 1 1⟩]⟩,default,default,default,default,default,default,default,default,default,default,⟨(0,1),[7],[⟨7,(2,3),.order false 1 1 1⟩]⟩,⟨(0,0),[17],[⟨17,(2,12),.order false 4 0 1⟩]⟩,⟨(0,0),[13],[⟨13,(2,5),.order false 2 1 1⟩]⟩,⟨(0,0),[5],[⟨5,(2,4),.order false 2 0 1⟩]⟩,⟨(0,0),[],[]⟩,⟨(0,0),[5, 11],[⟨5,(1,1),.pivot⟩, ⟨11,(4,6),.order true 1 0 5⟩]⟩,⟨(0,0),[37],[⟨37,(17,6),.order false 2 2 1⟩]⟩,⟨(0,0),[19],[⟨19,(8,6),.order false 1 2 1⟩]⟩,⟨(0,0),[17],[⟨17,(7,6),.order false 4 0 1⟩]⟩,⟨(0,0),[5, 7],[⟨5,(1,1),.pivot⟩, ⟨7,(2,6),.order false 1 1 1⟩]⟩,default,default,default,default,default,⟨(0,0),[7],[⟨7,(3,5),.order false 1 1 1⟩]⟩,⟨(0,0),[5],[⟨5,(2,3),.order false 2 0 1⟩]⟩,⟨(0,1),[],[]⟩,⟨(0,0),[],[]⟩,⟨(0,1),[],[]⟩,⟨(0,1),[5],[⟨5,(3,4),.order false 2 0 1⟩]⟩,⟨(0,0),[13],[⟨13,(7,5),.order false 2 1 1⟩]⟩,⟨(0,0),[11],[⟨11,(6,8),.order false 1 0 5⟩]⟩,⟨(0,0),[7],[⟨7,(4,3),.order false 1 1 1⟩]⟩,⟨(0,0),[5],[⟨5,(3,4),.order false 2 0 1⟩]⟩,default,default,default,default,default])[c.val*25+d.val*5+e.val]!

theorem tiny_match (c d e : Fin 5) (C : tinyCoeff c≠tinyCoeff d) (D : tinyCoeff c≠ -tinyCoeff d) :
    (tinyReceipt c d e).valid (tinyCoeff c) (tinyCoeff d) (tinyCoeff e) := by
  have H : ∀ i j k : Fin 5, tinyCoeff i≠tinyCoeff j → tinyCoeff i≠ -tinyCoeff j →
      (tinyReceipt i j k).valid (tinyCoeff i) (tinyCoeff j) (tinyCoeff k) := by decide +kernel
  exact H c d e C D

theorem tiny_index (c : Int) (C : surfaceIndex c) : ∃ k : Fin 5, tinyCoeff k=c := by
  rcases C with x|x|x|x|x <;> subst c
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩

theorem invert_surfaces_bad (c d e : Int) (C : surfaceIndex c) (D : surfaceIndex d) (E : surfaceIndex e)
    (a b : Kˣ) (H : pl a b (surfacePoly c)=0) (L : pl a⁻¹ b (surfacePoly d)=0)
    (M : pl a b⁻¹ (surfacePoly e)=0) (a1 : a≠1) (two : (2:K)≠0) (three : (3:K)≠0)
    (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (an : a^n=1) (bn : b^n=1) :
    ∃ p x y : Nat, p.Prime ∧ (p:K)=0 ∧ (a:K)=(x:K) ∧ (b:K)=(y:K) ∧ (p,x,y)∈exactBad := by
  obtain ⟨i,rfl⟩ := tiny_index c C
  obtain ⟨j,rfl⟩ := tiny_index d D
  obtain ⟨k,rfl⟩ := tiny_index e E
  obtain ⟨h,g,V,S⟩ := invert_surfaces _ _ _ C D a b H L M a1 two three
  exact (tinyReceipt i j k).sound _ _ _ (tiny_match i j k h g) a b n odd no3 two three an bn a1 V S

end RibbonD3Field
#print axioms RibbonD3Field.invert_surfaces_bad
