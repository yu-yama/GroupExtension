import GroupExtension.Basic
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

/-!
# Lemmas about extensions by Abelian groups

This file gives lemmas about group extensions `1 → N → E → G → 1` that hold when `N` is Abelian.

For the main definitions, see `GroupTheory/GroupExtension/Defs.lean`. For basic lemmas about general
group extensions, see `GroupTheory/GroupExtension/Basic.lean`.
-/

namespace groupCohomology

universe u
variable {k : Type u} {G : Type u} [CommRing k] [Group G] {A : Rep k G}

-- TODO: does Mathlib have these (or equivalent) lemmas?

lemma oneCocycles_ext_iff (f₁ f₂ : oneCocycles A) :
    f₁ = f₂ ↔ ∀ g : G, (f₁ : G → CoeSort.coe A) g = (f₂ : G → CoeSort.coe A) g :=
  ⟨fun a g ↦ congrFun (congrArg Subtype.val a) g, fun h ↦ Subtype.ext (funext fun g ↦ h g)⟩

lemma mem_oneCoboundaries_iff (f : oneCocycles A) :
    f ∈ oneCoboundaries A ↔
    ∃ x : CoeSort.coe A, ∀ g : G, A.ρ g x - x = (f : G → CoeSort.coe A) g := by
  apply exists_congr
  intro x
  simp only [LinearMap.codRestrict, dZero, LinearMap.coe_mk, AddHom.coe_mk, oneCocycles_ext_iff]

end groupCohomology

namespace SemidirectProduct

variable {N G : Type} [CommGroup N] [Group G] (φ : G →* MulAut N)

/-- The category of `ℤ`-linear `G`-representation with `φ` being the multiplicative action -/
noncomputable def toRep (φ : G →* MulAut N) : Rep ℤ G :=
  @Rep.ofMulDistribMulAction G N _ _ (MulDistribMulAction.compHom N φ)

instance : MulDistribMulAction G N := MulDistribMulAction.compHom N φ

/-- Turns a splitting into a corresponding 1-cocyle. -/
def splitting_toOneCocycle (s : (toGroupExtension φ).Splitting) :
    groupCohomology.oneCocycles (toRep φ) where
  val := fun g ↦ Additive.ofMul (α := N) (s.sectionHom g).left
  property := by
    rw [groupCohomology.mem_oneCocycles_iff (A := toRep φ)]
    intro g₁ g₂
    unfold toRep
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply, map_mul, mul_left, mul_comm, ← ofMul_mul]
    congr
    exact right_sectionHom s g₁

/-- Turns a 1-cocycle into a corresponding splitting. -/
def splitting_ofOneCocycle (f : groupCohomology.oneCocycles (toRep φ)) :
    (toGroupExtension φ).Splitting where
  sectionHom := {
    toFun := fun g ↦ ⟨Additive.toMul (f.val g), g⟩
    map_one' := by
      simp only [groupCohomology.oneCocycles_map_one, toMul_zero]
      rfl
    map_mul' := by
      unfold toRep at f
      intro g₁ g₂
      dsimp only
      rw [(groupCohomology.mem_oneCocycles_iff f.val).mp f.property g₁ g₂, toMul_add, mul_comm,
          Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul]
      rfl
  }
  rightHom_comp_sectionHom := by
    ext g
    rfl

/-- A bijection between the splittings and the 1-cocycles -/
def splitting_equiv_oneCocycles :
    (toGroupExtension φ).Splitting ≃ groupCohomology.oneCocycles (toRep φ) where
  toFun := splitting_toOneCocycle φ
  invFun := splitting_ofOneCocycle φ
  left_inv := by
    intro s
    unfold splitting_toOneCocycle splitting_ofOneCocycle
    congr
    ext g
    <;> congr
    <;> exact (s.rightHom_sectionHom g).symm
  right_inv := by
    intro f
    unfold splitting_toOneCocycle splitting_ofOneCocycle
    ext g
    simp only [mk_eq_inl_mul_inr, MonoidHom.coe_mk, OneHom.coe_mk, mul_left, left_inl, right_inl,
        map_one, left_inr, mul_one]
    rfl

/-- Two splittings are `N`-conjugates iff the difference of the corresponding 1-cocycles is a
    1-coboundary. -/
theorem isConj_iff_sub_mem_oneCoboundaries (s₁ s₂ : (toGroupExtension φ).Splitting) :
    (toGroupExtension φ).IsConj s₁ s₂ ↔
    splitting_toOneCocycle φ s₁ - splitting_toOneCocycle φ s₂ ∈
    groupCohomology.oneCoboundaries (toRep φ) := by
  rw [sub_mem_comm_iff, groupCohomology.mem_oneCoboundaries_iff]
  simp only [splitting_toOneCocycle, AddSubgroupClass.coe_sub, Pi.sub_apply]
  simp_rw [sub_eq_sub_iff_comm, eq_comm]
  apply exists_congr
  intro n
  rw [Function.funext_iff]
  apply forall_congr'
  intro g
  nth_rewrite 3 [show n = Additive.ofMul n by rfl]
  rw [show ((toRep φ).ρ g) n = Additive.ofMul (φ g n) by rfl, sub_eq_iff_eq_add, ← ofMul_div,
      ← ofMul_mul, Additive.ofMul.apply_eq_iff_eq, SemidirectProduct.ext_iff]
  simp only [mul_left, mul_right, inv_left, toGroupExtension_inl, left_inl, right_inl,
      MonoidHom.map_one, one_mul, inv_one, MulAut.one_apply, right_sectionHom, MulEquiv.map_inv,
      div_eq_mul_inv, mul_right_comm]
  apply and_iff_left
  rw [← rightHom_eq_right, MonoidHom.map_inv, rightHom_inl, inv_one, mul_one]

/-- A bijection between the `N`-conjugacy classes of splittings and `H1` -/
def conjClasses_equiv_h1 : (toGroupExtension φ).ConjClasses ≃ groupCohomology.H1 (toRep φ) :=
  Quotient.congr (splitting_equiv_oneCocycles φ) (by
    intro s₁ s₂
    rw [Submodule.quotientRel_r_def]
    exact isConj_iff_sub_mem_oneCoboundaries φ s₁ s₂
  )

end SemidirectProduct
