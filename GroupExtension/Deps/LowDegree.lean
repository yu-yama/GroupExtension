import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

namespace groupCohomology

universe u
variable {k : Type u} {G : Type u} [CommRing k] [Group G] {A : Rep k G}

example (f : oneCocycles A) (g h : G) : f (g * h) = A.ρ g (f h) + f g :=
  (mem_oneCocycles_iff f).mp f.property g h

example (f₁ f₂ : oneCocycles A) (g : G) : (f₁ - f₂) g = f₁ g - f₂ g := by
  rw [← oneCocycles.val_eq_coe, AddSubgroupClass.coe_sub, Pi.sub_apply]
  simp only [oneCocycles.val_eq_coe]

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
