import HaarMetaQuotientDispatchCore

namespace HaarMetaCyclic15Dispatch
open HaarMetaEarlyCases HaarMetaSmallDispatchCore HaarMetaPrimitiveDispatch
open HaarMetaQuotientDispatchCore HaarMetaAlgebraCore HaarClass4Generate
variable {G Q : Type*} [Group G] [CommGroup Q]

/-- The normalized cyclic-15 residues for the second torsion case reduce to
one of two primitive strip patterns. Callbacks keep the reduction independent
of the two strip certificates. -/
theorem cycle [Finite G] (f : G →* Q) (ab : ∀ a b : f.ker, a*b=b*a)
    (x y t : G) (hx : x≠1) (hy : y≠1) (ne : x≠y) (gen : Generates x y)
    (fx : f x≠1) (fy : f y≠1) (fne : f x≠f y)
    (card : Nat.card Q=15) (z : Q) (hz : Subgroup.zpowers z=⊤)
    (nt : f t≠1) (dt : (f t)^3=1) (dx : (f x)^3≠1)
    (eq : f y=(f x)^2*f t)
    (run3 : ∀ (g : G→*C 15) (X Y : G), (∀ a b : g.ker, a*b=b*a) →
      X≠1 → Y≠1 → X≠Y → Generates X Y →
      g X=Multiplicative.ofAdd (1:ZMod 15) → g Y=Multiplicative.ofAdd (3:ZMod 15) → Good X Y)
    (run4 : ∀ (g : G→*C 15) (X Y : G), (∀ a b : g.ker, a*b=b*a) →
      X≠1 → Y≠1 → X≠Y → Generates X Y →
      g X=Multiplicative.ofAdd (1:ZMod 15) → g Y=Multiplicative.ofAdd (4:ZMod 15) → Good X Y) :
    Good x y := by
  let ψ := HaarMetaCoordinateIso.orient z hz 15 card
  let F := ψ.toMonoidHom.comp f
  let a : ZMod 15 := (F t).toAdd
  let b : ZMod 15 := (F x).toAdd
  have nn : a≠0 := fun h => nt (ψ.injective (show F t=ψ 1 by rw [map_one]; exact h))
  have da : (3:ℕ) • a=0 := by
    change (F t)^3=1
    change (ψ (f t))^3=1; rw [←map_pow,dt,map_one]
  have db : (3:ℕ) • b≠0 := by
    intro h
    apply dx
    change (F x)^3=1 at h
    change (ψ (f x))^3=1 at h; rw [←map_pow] at h
    exact ψ.injective (h.trans (map_one ψ).symm)
  let u : Fin 15 := ⟨a.val, ZMod.val_lt a⟩
  let v : Fin 15 := ⟨b.val, ZMod.val_lt b⟩
  have PX : F x=Multiplicative.ofAdd (v.val:ZMod 15) :=
    congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val b).symm
  have PY : F y=Multiplicative.ofAdd ((2*v.val+u.val:ℕ):ZMod 15) := by
    change ψ (f y)=_
    rw [eq,map_mul,map_pow]
    change (F x)^2 * F t = _
    rw [PX]
    change (2:ℕ) • (v.val:ZMod 15) + a = _
    simp only [u, Nat.cast_add, ZMod.natCast_zmod_val, two_nsmul, two_mul]; rfl
  have ds := from_projection F x y _ _ PX PY
    (fun h => fx (ψ.injective (h.trans (map_one ψ).symm)))
    (fun h => fy (ψ.injective (h.trans (map_one ψ).symm)))
    (fun h => fne (ψ.injective h))
  have aff := HaarMetaSmallAffine.torsion15_shift u v (zmod15_gen a b nn da db) ds
  rcases aff with h|h
  · exact apply_affine F x y _ _ 1 3 (ab_kernel_comp f ψ.toMonoidHom ψ.injective ab)
      hx hy ne gen PX PY (by decide) (by decide) (by decide) (by decide) (by decide) h run3
  · exact apply_affine F x y _ _ 1 4 (ab_kernel_comp f ψ.toMonoidHom ψ.injective ab)
      hx hy ne gen PX PY (by decide) (by decide) (by decide) (by decide) (by decide) h run4

end HaarMetaCyclic15Dispatch
#print axioms HaarMetaCyclic15Dispatch.cycle
