import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

namespace groupCohomology

universe u
variable {k : Type u} {G : Type u} [CommRing k] [Group G] {A : Rep k G}

-- TODO: does Mathlib have these (or equivalent) lemmas?

lemma oneCocycles_ext_iff (f₁ f₂ : oneCocycles A) :
    f₁ = f₂ ↔ ∀ g : G, (f₁ : G → CoeSort.coe A) g = (f₂ : G → CoeSort.coe A) g :=
  ⟨fun h g ↦ congrFun (congrArg Subtype.val h) g, fun h ↦ Subtype.ext (funext fun g ↦ h g)⟩

example (f₁ f₂ : oneCocycles A) :
    f₁ = f₂ ↔ ∀ g : G, (f₁ : G → CoeSort.coe A) g = (f₂ : G → CoeSort.coe A) g := by
  rw [← funext_iff, Subtype.val_inj]

lemma mem_oneCoboundaries_iff (f : oneCocycles A) :
    f ∈ oneCoboundaries A ↔
    ∃ x : CoeSort.coe A, ∀ g : G, A.ρ g x - x = (f : G → CoeSort.coe A) g := by
  apply exists_congr
  intro x
  simp only [LinearMap.codRestrict, dZero, LinearMap.coe_mk, AddHom.coe_mk, oneCocycles_ext_iff]

lemma twoCocycles_ext_iff (f₁ f₂ : twoCocycles A) :
    f₁ = f₂ ↔
    ∀ g h : G, (f₁ : G × G → CoeSort.coe A) (g, h) = (f₂ : G × G → CoeSort.coe A) (g, h) :=
  ⟨fun hf g h ↦ congrFun (congrArg Subtype.val hf) (g, h),
    fun hf ↦ Subtype.ext (funext fun ⟨g, h⟩ ↦ hf g h)⟩

lemma mem_twoCoboundaries_iff (f : twoCocycles A) :
    f ∈ twoCoboundaries A ↔
    ∃ x : G → CoeSort.coe A, ∀ g h : G, A.ρ g (x h) - x (g * h) + x g = f.val (g, h) := by
  apply exists_congr
  intro x
  simp only [LinearMap.codRestrict, dOne, LinearMap.coe_mk, AddHom.coe_mk, twoCocycles_ext_iff]

-- TODO: should we instantiate `FunLike` for (one|two)Co(cycles|boundaries)?
-- instance : FunLike (oneCocycles A) G (CoeSort.coe A) := ⟨(·.val), Subtype.val_injective⟩
-- instance : FunLike (twoCocycles A) (G × G) (CoeSort.coe A) := ⟨(·.val), Subtype.val_injective⟩
-- instance : FunLike (oneCoboundaries A) G (CoeSort.coe A) :=
--   ⟨(·.val), Function.Injective.comp Subtype.val_injective Subtype.val_injective⟩
-- instance : FunLike (twoCoboundaries A) (G × G) (CoeSort.coe A) :=
--   ⟨(·.val), Function.Injective.comp Subtype.val_injective Subtype.val_injective⟩

variable (A)

structure normalizedTwoCocycles where
  toTwoCocycles : twoCocycles A
  map_one_one : toTwoCocycles.val ⟨1, 1⟩ = 0

variable {A}

theorem normalizedTwoCocycles_map_one_fst (f : normalizedTwoCocycles A) (g : G) :
    f.toTwoCocycles.val ⟨1, g⟩ = 0 := by
  rw [twoCocycles_map_one_fst, f.map_one_one]

theorem normalizedTwoCocycles_map_one_snd (f : normalizedTwoCocycles A) (g : G) :
    f.toTwoCocycles.val ⟨g, 1⟩ = 0 := by
  rw [twoCocycles_map_one_snd, f.map_one_one, map_zero]

theorem normalizedTwoCocycles_ρ_map_inv_eq_map_inv (f : normalizedTwoCocycles A) (g : G) :
    (A.ρ g) (f.toTwoCocycles.val ⟨g⁻¹, g⟩) = f.toTwoCocycles.val ⟨g, g⁻¹⟩ := by
  rw [← sub_eq_zero, twoCocycles_ρ_map_inv_sub_map_inv, sub_eq_zero,
    f.map_one_one, normalizedTwoCocycles_map_one_snd]

-- instance : FunLike (normalizedTwoCocycles A) (G × G) (CoeSort.coe A) := ⟨(·.toTwoCocycles), Subtype.val_injective⟩

end groupCohomology
