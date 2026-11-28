import AtlasCoverage
import AtlasPack
import AtlasMarked

namespace BikovEight

def Extends (G : Fin 8→Fin 8→Prop) (c : Fin 8→Fin 8→Bool) : Prop :=
  ∃ f : Fin 8→Bool, ∀ a b, G a b→¬(f a=c a b ∧ f b=c a b)

/-- Every triangle-free marked eight-vertex link belongs toG Bikov's atlas.
The witness is a concrete vertex permutation to a named graph. -/
theorem marked_atlas (G : Fin 8→Fin 8→Prop)
    (sym : ∀ a b,G a b→G b a) (irr : ∀ a,¬G a a)
    (tri : ∀ a b c,G a b→G a c→G b c→False)
    (c : Fin 8→Fin 8→Bool) (cs : ∀ a b,c a b=c b a)
    (blocked : ¬Extends G c) :
    ∃ i : Fin 7, ∃ σ : Equiv.Perm (Fin 8), ∀ a b,
      G (σ a) (σ b) ↔ Erdos151MarkedLinkTable.adj i a b=true := by
  classical
  rcases classify_walk8 G (fun {_ _} h=>sym _ _ h) irr tri with ⟨f,h⟩|⟨k,kk,σ,shape⟩
  · exact False.elim (blocked ⟨f,fun a b e x=>h e (x.1.trans x.2.symm)⟩)
  let S (a b : Fin 8) := G (σ a) (σ b)
  let lab (a b : Fin 8) := c (σ a) (σ b)
  have ss (a b : Fin 8) (h : S a b) : S b a := sym _ _ h
  have si (a : Fin 8) : ¬S a a := irr _
  have st (a b d : Fin 8) : S a b→S a d→S b d→False := tri _ _ _
  have ls (a b : Fin 8) : lab a b=lab b a := cs _ _
  have blockS : ¬Extends S lab := by
    intro ⟨f,h⟩
    apply blocked
    refine ⟨fun a=>f (σ.symm a),?_⟩
    intro a b e x
    have s : S (σ.symm a) (σ.symm b) := by simpa [S] using e
    apply h _ _ s
    simpa [lab] using x
  rcases kk with rfl|rfl
  · obtain ⟨h,hB,hV,toG⟩ := normalized5 (G:=S) ss si st shape
    obtain ⟨v,vr⟩ := cover5 h hB hV
    rcases check_sound (word5 h) v vr with cut|⟨i,ρ,w⟩
    · obtain ⟨f,ff⟩ := cut lab ls
      exact False.elim (blockS ⟨f,fun a b e=>ff a b ((toG a b).mpr e)⟩)
    · exact ⟨i,ρ.trans σ,fun a b=>((toG (ρ a) (ρ b)).symm.trans (w a b))⟩
  · obtain ⟨p,hB,hV,toG⟩ := normalized7 (G:=S) ss si st shape
    obtain ⟨v,vr⟩ := cover7 p hB hV
    obtain ⟨f,ff⟩ := cut_sound (make7 p) v vr lab ls
    exact False.elim (blockS ⟨f,fun a b e=>ff a b ((toG a b).mpr e)⟩)

def IsMarked (G : Fin 8→Fin 8→Prop) : Prop :=
  ∃ c : Fin 8→Fin 8→Bool, (∀ a b,c a b=c b a) ∧ ¬Extends G c

/-- The exact atlas, including certificates showing that each named model
really blocks a symmetric edge coloring. -/
theorem marked_iff_atlas (G : Fin 8→Fin 8→Prop)
    (sym : ∀ a b,G a b→G b a) (irr : ∀ a,¬G a a)
    (tri : ∀ a b c,G a b→G a c→G b c→False) :
    IsMarked G ↔
    (∃ i : Fin 7, ∃ σ : Equiv.Perm (Fin 8), ∀ a b,
      G (σ a) (σ b) ↔ Erdos151MarkedLinkTable.adj i a b=true) := by
  constructor
  · rintro ⟨c,cs,h⟩
    exact marked_atlas G sym irr tri c cs h
  · rintro ⟨i,σ,m⟩
    obtain ⟨cs,h⟩ := each_name_marked i
    let c (a b : Fin 8) := color i (σ.symm a) (σ.symm b)
    refine ⟨c,fun a b=>cs _ _,?_⟩
    intro ⟨f,k⟩
    obtain ⟨a,b,e,p,q⟩ := h (fun a=>f (σ a))
    apply k (σ a) (σ b) ((m a b).mpr e)
    simpa [c] using And.intro p q

#print axioms marked_atlas
#print axioms marked_iff_atlas
end BikovEight
