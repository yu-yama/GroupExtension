import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

namespace groupCohomology

universe u
variable {k : Type u} {G : Type u} [CommRing k] [Group G] {A : Rep k G}

lemma oneCocycles_ext_iff (f₁ f₂ : oneCocycles A) :
    f₁ = f₂ ↔ ∀ g : G, f₁.1 g = f₂.1 g :=
  ⟨fun h g ↦ congrFun (congrArg Subtype.val h) g, fun h ↦ Subtype.ext (funext fun g ↦ h g)⟩

lemma mem_oneCoboundaries_iff (f : oneCocycles A) :
    f ∈ oneCoboundaries A ↔
    ∃ x : A, ∀ g : G, A.ρ g x - x = f.1 g := by
  apply exists_congr
  intro x
  simp only [LinearMap.codRestrict, dZero, LinearMap.coe_mk, AddHom.coe_mk, oneCocycles_ext_iff]

lemma twoCocycles_ext_iff (f₁ f₂ : twoCocycles A) :
    f₁ = f₂ ↔
    ∀ g h : G, f₁.1 (g, h) = f₂.1 (g, h) :=
  ⟨fun hf g h ↦ congrFun (congrArg Subtype.val hf) (g, h),
    fun hf ↦ Subtype.ext (funext fun ⟨g, h⟩ ↦ hf g h)⟩

lemma mem_twoCoboundaries_iff (f : twoCocycles A) :
    f ∈ twoCoboundaries A ↔
    ∃ x : G → A, ∀ g h : G, A.ρ g (x h) - x (g * h) + x g = f.1 (g, h) := by
  apply exists_congr
  intro x
  simp only [LinearMap.codRestrict, dOne, LinearMap.coe_mk, AddHom.coe_mk, twoCocycles_ext_iff]

end groupCohomology

-- A use case
example {G A : Type} [Group G] [CommGroup A] [MulDistribMulAction G A]
    {f f' : groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G A)}
    (h : f - f' ∈ groupCohomology.twoCoboundaries (Rep.ofMulDistribMulAction G A)) :
    ∃ x : G → A, ∀ g₁ g₂ : G, Additive.toMul (α := A) (f.1 (g₁, g₂)) *
    (Additive.toMul (α := A) (f'.1 (g₁, g₂)))⁻¹ = g₁ • x g₂ * (x (g₁ * g₂))⁻¹ * x g₁ := by
  rw [groupCohomology.mem_twoCoboundaries_iff] at h
  obtain ⟨x, hx⟩ := h
  use fun g ↦ Additive.toMul (x g)
  intro g₁ g₂
  simpa only [Rep.ofMulDistribMulAction_ρ_apply_apply, ← div_eq_mul_inv]
    using Additive.toMul.injective (hx g₁ g₂).symm
