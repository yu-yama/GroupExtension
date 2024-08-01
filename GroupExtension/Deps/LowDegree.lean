import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

namespace groupCohomology

universe u
variable {k : Type u} {G : Type u} [CommRing k] [Group G] {A : Rep k G}

-- TODO: does Mathlib have these (or equivalent) lemmas?

lemma oneCocycles_ext_iff (f₁ f₂ : oneCocycles A) :
    f₁ = f₂ ↔ ∀ g : G, (f₁ : G → CoeSort.coe A) g = (f₂ : G → CoeSort.coe A) g :=
  ⟨fun h g ↦ congrFun (congrArg Subtype.val h) g, fun h ↦ Subtype.ext (funext fun g ↦ h g)⟩

lemma mem_oneCoboundaries_iff (f : oneCocycles A) :
    f ∈ oneCoboundaries A ↔
    ∃ x : CoeSort.coe A, ∀ g : G, A.ρ g x - x = (f : G → CoeSort.coe A) g := by
  apply exists_congr
  intro x
  simp only [LinearMap.codRestrict, dZero, LinearMap.coe_mk, AddHom.coe_mk, oneCocycles_ext_iff]

end groupCohomology
