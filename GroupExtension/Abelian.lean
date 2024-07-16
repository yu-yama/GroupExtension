import GroupExtension.Basic
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

variable {N G : Type} [CommGroup N] [Group G]

namespace SemidirectProduct

variable (φ : G →* MulAut N)

noncomputable def toRep (φ : G →* MulAut N) : Rep ℤ G := @Rep.ofMulDistribMulAction G N _ _ (MulDistribMulAction.compHom N φ)

def splitting_toOneCocycle (s : (toGroupExtension φ).Splitting)
  : groupCohomology.oneCocycles (toRep φ) where
  val := fun g ↦ Additive.ofMul (s.sectionHom g).left
  property := by
    rw [groupCohomology.mem_oneCocycles_iff]
    intro g₁ g₂
    unfold toRep
    -- have h : CoeSort.coe (toRep φ) = N := by rfl
    -- have h : CoeSort.coe (@Rep.ofMulDistribMulAction G N _ _ (MulDistribMulAction.compHom N φ)) = N := by rfl
    dsimp only [Rep.ofMulDistribMulAction_ρ_apply_apply]
    -- rw [map_mul, mul_left, mul_comm, ← ofMul_mul]
    -- simp only [map_mul, mul_left, ofMul_mul, Rep.ofMulDistribMulAction_ρ_apply_apply]
    -- unfold toRep
    -- rw [add_comm, add_left_cancel_iff]
    -- rfl
    -- rw [Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul, ← ofMul_mul]
    sorry

def splitting_ofOneCocycle (f : groupCohomology.oneCocycles (toRep φ))
  : (toGroupExtension φ).Splitting where
  sectionHom := {
    toFun := fun g ↦ ⟨Additive.toMul (f.val g), g⟩
    map_one' := by
      simp only [groupCohomology.oneCocycles_map_one, toMul_zero]
      rfl
    map_mul' := by
      unfold toRep at f
      intro g₁ g₂
      dsimp only
      rw [(groupCohomology.mem_oneCocycles_iff f.val).mp f.property g₁ g₂, toMul_add, mul_comm, Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul]
      rfl
  }
  rightHom_comp_sectionHom := by
    ext g
    rfl

def splitting_equiv_oneCocycles
  : (toGroupExtension φ).Splitting ≃ groupCohomology.oneCocycles (toRep φ) where
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
    simp only [mk_eq_inl_mul_inr, MonoidHom.coe_mk, OneHom.coe_mk, mul_left, left_inl, right_inl, map_one, left_inr, mul_one]
    sorry

end SemidirectProduct

namespace GroupExtension

end GroupExtension
