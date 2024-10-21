import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

namespace groupCohomology

universe u
variable {k : Type u} {G : Type u} [CommRing k] [Group G] {A : Rep k G}

instance : FunLike (oneCocycles A) G A := ⟨(·.val), Subtype.val_injective⟩

@[ext]
theorem oneCocycles_ext {f₁ f₂ : oneCocycles A} (h : ∀ g : G, f₁ g = f₂ g) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ h

instance : FunLike (twoCocycles A) (G × G) A := ⟨(·.val), Subtype.val_injective⟩

@[ext]
theorem twoCocycles_ext {f₁ f₂ : twoCocycles A} (h : ∀ g h : G, f₁ (g, h) = f₂ (g, h)) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ (Prod.forall.mpr h)

theorem mem_oneCoboundaries_iff (f : oneCocycles A) : f ∈ oneCoboundaries A ↔
    ∃ x : A, ∀ g : G, A.ρ g x - x = f g := exists_congr fun x ↦ by
  simpa only [LinearMap.codRestrict, dZero, LinearMap.coe_mk, AddHom.coe_mk] using
    groupCohomology.oneCocycles_ext_iff

theorem mem_twoCoboundaries_iff (f : twoCocycles A) : f ∈ twoCoboundaries A ↔
    ∃ x : G → A, ∀ g h : G, A.ρ g (x h) - x (g * h) + x g = f (g, h) := exists_congr fun x ↦ by
  simpa only [LinearMap.codRestrict, dOne, LinearMap.coe_mk, AddHom.coe_mk] using
    groupCohomology.twoCocycles_ext_iff

end groupCohomology

-- A use case
example {G A : Type} [Group G] [CommGroup A] [MulDistribMulAction G A]
    {f f' : groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G A)}
    (h : f - f' ∈ groupCohomology.twoCoboundaries (Rep.ofMulDistribMulAction G A)) :
    ∃ x : G → A, ∀ g₁ g₂ : G, Additive.toMul (α := A) (f (g₁, g₂)) *
    (Additive.toMul (α := A) (f' (g₁, g₂)))⁻¹ = g₁ • x g₂ * (x (g₁ * g₂))⁻¹ * x g₁ := by
  rw [groupCohomology.mem_twoCoboundaries_iff] at h
  obtain ⟨x, hx⟩ := h
  use fun g ↦ Additive.toMul (x g)
  intro g₁ g₂
  simpa only [Rep.ofMulDistribMulAction_ρ_apply_apply, ← div_eq_mul_inv]
    using Additive.toMul.injective (hx g₁ g₂).symm
