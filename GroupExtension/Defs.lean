import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SemidirectProduct

variable (N E G : Type*) [Group N] [Group E] [Group G]

/-- `GroupExtension N E G` is a short exact sequence of (multiplicative) groups `1 → N → E → G → 1` -/
structure GroupExtension where
  /-- The inclusion homomorphism `N →* E` -/
  inl : N →* E
  /-- The projection homomorphism `E →* G` -/
  rightHom : E →* G
  /-- The inclusion map is injective -/
  inl_injective : Function.Injective inl
  /-- The range of the inclusion map is equal to the kernel of the projection map -/
  range_inl_eq_ker_rightHom : inl.range = rightHom.ker
  /-- The projection map is surjective -/
  rightHom_surjective : Function.Surjective rightHom

variable {N E G}

namespace GroupExtension

variable (S : GroupExtension N E G)

/-- The range of the inclusion map is a normal subgroup -/
instance normal_inl_range : (S.inl.range).Normal := by
  rw [S.range_inl_eq_ker_rightHom]
  exact MonoidHom.normal_ker S.rightHom

theorem rightHom_inl {n : N} : S.rightHom (S.inl n) = 1 := by
  rw [← MonoidHom.mem_ker, ← S.range_inl_eq_ker_rightHom, MonoidHom.mem_range]
  exact exists_apply_eq_apply S.inl n

theorem rightHom_comp_inl : S.rightHom.comp S.inl = 1 := by
  ext n
  rw [MonoidHom.one_apply, MonoidHom.comp_apply]
  exact S.rightHom_inl

-- TODO: is there a Mathlib shorthand to compose the homomorphism `conjAct`?
/-- `E` acts on `N` by conjugation -/
noncomputable def conjAct : E →* MulAut N := {
  toFun := fun e ↦ (MonoidHom.ofInjective S.inl_injective).trans <| (MulAut.conjNormal e).trans (MonoidHom.ofInjective S.inl_injective).symm
  map_one' := by
    ext _
    simp only [map_one, MulEquiv.trans_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  map_mul' := fun _ _ ↦ by
    ext _
    simp only [map_mul, MulEquiv.trans_apply, MulAut.mul_apply, MulEquiv.apply_symm_apply]
}

/-- The inclusion and a conjugation commute -/
theorem inl_conjAct_comm {e : E} {n : N} : S.inl (S.conjAct e n) = e * S.inl n * e⁻¹ := by
  simp only [conjAct, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm]
  rfl

/-- `Splitting` of a group extension is a section homomorphism -/
structure Splitting where
  /-- A section homomorphism -/
  sectionHom : G →* E
  /-- The section is a left inverse of the projection map -/
  rightHom_comp_sectionHom : S.rightHom.comp sectionHom = MonoidHom.id G

/-- `GroupExtension`s are equivalent iff there is a homomorphism making a commuting diagram -/
structure Equiv {E' : Type*} [Group E'] (S' : GroupExtension N E' G) where
  /-- The homomorphism -/
  toMonoidHom : E →* E'
  /-- The left-hand side of the diagram commutes -/
  inl_comm : S'.inl = toMonoidHom.comp S.inl
  /-- The right-hand side of the diagram commutes -/
  rightHom_comm : S.rightHom = S'.rightHom.comp toMonoidHom

end GroupExtension

namespace SemidirectProduct

variable (φ : G →* MulAut N)

/-- A canonical group extension giving a semidirect product -/
def toGroupExtension : GroupExtension N (N ⋊[φ] G) G where
  inl_injective := inl_injective
  range_inl_eq_ker_rightHom := range_inl_eq_ker_rightHom
  rightHom_surjective := rightHom_surjective

/-- A canonical splitting -/
def inr_splitting : (toGroupExtension φ).Splitting where
  sectionHom := inr
  rightHom_comp_sectionHom := rightHom_comp_inr

end SemidirectProduct
