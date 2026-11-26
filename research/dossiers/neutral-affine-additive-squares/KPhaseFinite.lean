import KPhase

namespace KPhaseFinite
open KPhase KProjection

variable {D : Finset ℤ} {f : ℤ → List ℤ} {k : ℕ}
variable (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)
variable (u v : ℤ × ℤ) (neg : Bool) (m B : ℤ)

abbrev VW := VectorWalk.Walk (src (D:=D) (f:=f) (k:=k) (v:=v) (m:=m) (B:=B))
  (dst closed v neg m B) (label u v neg m B)

theorem from_walk {x y : Vertex D k B} {w : Fin k → ℤ}
    (h : VW closed u v neg m B x y w) :
    ∃ L, KTrace.Path D f k closed x.1 y.1 L ∧
      aug closed v neg m (into B x) L = into B y ∧ costs u neg x.2.2 L = w := by
  induction h with
  | nil x => exact ⟨[],.nil _,rfl,rfl⟩
  | cons e h ih =>
    obtain ⟨L,p,a,c⟩ := ih
    exact ⟨e.val.1::L,.cons _ p,a, congrArg (fun x => label u v neg m B e + x) c⟩

theorem to_walk {x y : Q D k} {L : List (E D f k)} (h : KTrace.Path D f k closed x y L)
    (p : Fin k → ℤ) (q : Bool)
    (hp : ∀ U V, L = U ++ V → ∀ j, (aug closed v neg m ⟨x,p,q⟩ U).x j ∈ IntegerTrace.box B) :
    ∃ (h₁ : ∀ j, p j ∈ IntegerTrace.box B)
      (h₂ : ∀ j, (aug closed v neg m ⟨x,p,q⟩ L).x j ∈ IntegerTrace.box B),
      VW closed u v neg m B (pack B ⟨x,p,q⟩ h₁) (pack B (aug closed v neg m ⟨x,p,q⟩ L) h₂) (costs u neg q L) := by
  induction h generalizing p q with
  | nil x =>
    have hx : ∀ j, p j ∈ IntegerTrace.box B := hp [] [] rfl
    exact ⟨hx,hx,.nil _⟩
  | @cons e y L h ih =>
    have h₀ : ∀ j, p j ∈ IntegerTrace.box B := hp [] (e::L) rfl
    let np := next closed v neg m e ⟨KFinite.src e,p,q⟩
    have hstep : ∀ U V, L = U ++ V → ∀ j,
        (aug closed v neg m ⟨KFinite.dst closed e,np.x,np.bit⟩ U).x j ∈ IntegerTrace.box B := by
      intro U V eq
      exact hp (e::U) V (congrArg (e::·) eq)
    obtain ⟨h₁,h₂,w⟩ := ih np.x np.bit hstep
    let t : Arc D f k v m B := ⟨⟨e,fun j => ⟨p j,h₀ j⟩,q⟩,h₁⟩
    exact ⟨h₀,h₂,.cons t w⟩

def target (y : Q D k) (z : 0 ∈ IntegerTrace.box B) (q : Bool) : Vertex D k B :=
  ⟨y,fun _ => ⟨0,z⟩,q⟩

theorem criterion (x y : Q D k) (z : 0 ∈ IntegerTrace.box B) (C : ℤ)
    (hE : ∀ (e : E D f k) (j : Fin k), |ex v j e| ≤ C)
    (ha : 1 < |m|) (hB : 0 ≤ B) (hc : C ≤ (|m|-1)*B) :
    (∃ q, VW closed u v neg m B (target B x z false) (target B y z q) 0) ↔
    ∃ L, KTrace.Path D f k closed x y L ∧
      (∀ j : Fin k, ScalarTrace.zeval (PhaseProduct.sign neg) 0 (L.map (nu u j)) = 0) ∧
      (∀ j : Fin k, ScalarTrace.zeval m 0 (L.map (ex v j)) = 0) := by
  constructor
  · rintro ⟨q,h⟩
    obtain ⟨L,p,a,c⟩ := from_walk closed u v neg m B h
    refine ⟨L,p,(zero_iff closed u v neg m x false L).mpr c,?_⟩
    intro j
    have hx : (aug closed v neg m ⟨x,0,false⟩ L).x j = 0 :=
      congrArg (fun p : PNode (Q D k) k => p.x j) a
    exact (aug_x closed u v neg m ⟨x,0,false⟩ L j).symm.trans hx
  · rintro ⟨L,hp,hn,he⟩
    let p : PNode (Q D k) k := ⟨x,0,false⟩
    have safe : ∀ U V, L = U ++ V → ∀ j,
        (aug closed v neg m p U).x j ∈ IntegerTrace.box B := by
      intro U V h j
      rw [aug_x closed u v neg m]
      exact all_prefix v m B C ha hB hc hE L U V h he j
    obtain ⟨h₁,h₂,w⟩ := to_walk closed u v neg m B hp 0 false safe
    let e := aug closed v neg m p L
    have fin : pack B e h₂ = target B y z e.bit := by
      apply Prod.ext
      · exact aug_loc closed v neg m 0 false hp
      apply Prod.ext
      · funext j
        apply Subtype.ext
        exact (aug_x closed u v neg m p L j).trans (he j)
      · rfl
    have hz := (zero_iff closed u v neg m x false L).mp hn
    change VW closed u v neg m B (target B x z false) (pack B e h₂) (costs u neg false L) at w
    rw [fin,hz] at w
    exact ⟨e.bit,w⟩

end KPhaseFinite

#print axioms KPhaseFinite.from_walk
#print axioms KPhaseFinite.to_walk
#print axioms KPhaseFinite.criterion
