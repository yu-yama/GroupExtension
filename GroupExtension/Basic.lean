import GroupExtension.Defs
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.Tactic.Group

/-!
# Basic lemmas about group extensions

This file gives basic lemmas about group extensions.

For the main definitions, see `GroupTheory/GroupExtension/Defs.lean`.
-/

variable {N G : Type*} [Group N] [Group G]

namespace GroupExtension

variable {E : Type*} [Group E] (S : GroupExtension N E G)

noncomputable def quotientKerRightHomEquivRight : E ⧸ S.rightHom.ker ≃* G :=
  QuotientGroup.quotientKerEquivOfSurjective S.rightHom S.rightHom_surjective
noncomputable def quotientRangeInlEquivRight : E ⧸ S.inl.range ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq S.range_inl_eq_ker_rightHom).trans S.quotientKerRightHomEquivRight

theorem conjAct_one : S.conjAct 1 = 1 := by
  ext _
  apply S.inl_injective
  rw [inl_conjAct_comm, inv_one, mul_one, one_mul, MulAut.one_apply]

theorem rightHom_eq_iff_exists_inl_mul {e e' : E} :
    S.rightHom e = S.rightHom e' ↔ ∃ n : N, S.inl n * e' = e := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, ← S.range_inl_eq_ker_rightHom]
  exact exists_congr <| fun _ ↦ eq_mul_inv_iff_mul_eq

/-- A set-theoretic section that maps `1 : G` to `1 : E` -/
noncomputable def sectionOneHom : OneHom G E where
  toFun :=
    haveI := Classical.decEq G
    fun g ↦ if g = 1 then 1 else Function.surjInv S.rightHom_surjective g
  map_one' := if_pos rfl

theorem rightHom_sectionOneHom (g : G) : S.rightHom (S.sectionOneHom g) = g := by
  by_cases h : g = 1
  ·
    simp only [h, map_one]
  ·
    unfold sectionOneHom
    simp only [OneHom.coe_mk, if_neg h, Function.surjInv_eq S.rightHom_surjective]

-- TODO: rename properly
theorem sectionOneHom_mul_mul_mul_inv_mem_range (g₁ g₂ : G) :
    S.sectionOneHom g₁ * S.sectionOneHom g₂ * (S.sectionOneHom (g₁ * g₂))⁻¹ ∈ S.inl.range := by
  rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  simp only [map_mul, map_inv, rightHom_sectionOneHom, mul_inv_self]

namespace Equiv

variable {S}
variable {E' : Type*} [Group E'] {S' : GroupExtension N E' G} (equiv : S.Equiv S')

/-- Short exact sequences of equivalent group extensions commute -/
theorem comm : S.rightHom.comp S.inl = S'.rightHom.comp S'.inl := by
  rw [← equiv.rightHom_comm, MonoidHom.comp_assoc, equiv.inl_comm]

/-- The four lemma (deriving injectivity) specialized for group extensions -/
theorem injective : Function.Injective equiv.toMonoidHom := by
  rw [injective_iff_map_eq_one]
  intro e he
  have he' := congrArg S'.rightHom he
  rw [S'.rightHom.map_one, ← MonoidHom.comp_apply, equiv.rightHom_comm, ← MonoidHom.mem_ker,
    ← S.range_inl_eq_ker_rightHom] at he'
  obtain ⟨n, rfl⟩ := he'
  rw [← MonoidHom.comp_apply, equiv.inl_comm,
    (injective_iff_map_eq_one' S'.inl).mp S'.inl_injective] at he
  rw [he, S.inl.map_one]

/-- The four lemma (deriving surjectivity) specialized for group extensions -/
theorem surjective : Function.Surjective equiv.toMonoidHom := by
  intro e'
  obtain ⟨e, he⟩ := S.rightHom_surjective (S'.rightHom e')
  rw [eq_comm, ← equiv.rightHom_comm, MonoidHom.comp_apply, MonoidHom.eq_iff,
    ← S'.range_inl_eq_ker_rightHom] at he
  obtain ⟨n, hn⟩ := he
  use e * S.inl n
  rw [MonoidHom.map_mul, ← MonoidHom.comp_apply, equiv.inl_comm, hn, mul_inv_cancel_left]

/-- The five lemma specialized for group extensions -/
theorem bijective : Function.Bijective equiv.toMonoidHom := ⟨equiv.injective, equiv.surjective⟩

/-- A homomorphism between equivalent group extensions is indeed an isomorphism -/
noncomputable def toMulEquiv : E ≃* E' := MulEquiv.ofBijective equiv.toMonoidHom equiv.bijective

theorem toMonoidHom_eq_toMulEquiv : equiv.toMonoidHom = equiv.toMulEquiv := rfl

def refl (S : GroupExtension N E G) : S.Equiv S where
  toMonoidHom := MonoidHom.id E
  inl_comm := MonoidHom.id_comp _
  rightHom_comm := MonoidHom.comp_id _

noncomputable def symm : S'.Equiv S where
  toMonoidHom := equiv.toMulEquiv.symm
  inl_comm := by
    rw [← equiv.inl_comm, ← MonoidHom.comp_assoc, toMonoidHom_eq_toMulEquiv,
      MulEquiv.coe_monoidHom_symm_comp_coe_monoidHom, MonoidHom.id_comp]
  rightHom_comm := by
    rw [← equiv.rightHom_comm, MonoidHom.comp_assoc, toMonoidHom_eq_toMulEquiv,
      MulEquiv.coe_monoidHom_comp_coe_monoidHom_symm, MonoidHom.comp_id]

def trans {E'' : Type*} [Group E''] {S'' : GroupExtension N E'' G} (equiv' : S'.Equiv S'') :
    S.Equiv S'' where
  toMonoidHom := equiv'.toMonoidHom.comp equiv.toMonoidHom
  inl_comm := by rw [MonoidHom.comp_assoc, equiv.inl_comm, equiv'.inl_comm]
  rightHom_comm := by rw [← MonoidHom.comp_assoc, equiv'.rightHom_comm, equiv.rightHom_comm]

end Equiv

namespace Splitting

variable {S}
variable (s : S.Splitting)

theorem rightHom_sectionHom (g : G) : S.rightHom (s.sectionHom g) = g := by
  rw [← MonoidHom.comp_apply, s.rightHom_comp_sectionHom, MonoidHom.id_apply]

/-- `G` acts on `N` by conjugation -/
noncomputable def conjAct : G →* MulAut N := S.conjAct.comp s.sectionHom

/-- A group homomorphism from the corresponding semidirect product -/
def monoidHom_semidirectProduct : N ⋊[s.conjAct] G →* E where
  toFun := fun ⟨n, g⟩ ↦ S.inl n * s.sectionHom g
  map_one' := by simp only [map_one, mul_one]
  map_mul' := fun ⟨n₁, g₁⟩ ⟨n₂, g₂⟩ ↦ by
    simp only [conjAct, MonoidHom.comp_apply, map_mul, inl_conjAct_comm]
    group

/-- A split group extension is equivalent to a canonical extension giving a semidirect product. -/
def equiv_semidirectProduct : (SemidirectProduct.toGroupExtension s.conjAct).Equiv S where
  toMonoidHom := monoidHom_semidirectProduct s
  inl_comm := by
    ext n
    simp only [SemidirectProduct.toGroupExtension, MonoidHom.comp_apply,
      monoidHom_semidirectProduct, MonoidHom.coe_mk, OneHom.coe_mk, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, mul_one]
  rightHom_comm := by
    ext ⟨n, g⟩
    simp only [SemidirectProduct.toGroupExtension, MonoidHom.comp_apply,
      SemidirectProduct.rightHom_eq_right, monoidHom_semidirectProduct, MonoidHom.coe_mk,
      OneHom.coe_mk, map_mul, rightHom_inl, rightHom_sectionHom, one_mul]

/-- A group given by a split extension is isomorphic to a semidirect product -/
noncomputable def mulEquiv_semidirectProduct : N ⋊[s.conjAct] G ≃* E :=
  s.equiv_semidirectProduct.toMulEquiv

end Splitting

namespace IsConj

/-- `N`-conjugacy is reflexive. -/
theorem refl (s : S.Splitting) : S.IsConj s s :=
  ⟨1, by simp only [map_one, inv_one, one_mul, mul_one]⟩

/-- `N`-conjugacy is symmetric. -/
theorem symm {s₁ s₂ : S.Splitting} (h : S.IsConj s₁ s₂) : S.IsConj s₂ s₁ := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n⁻¹, by simp only [hn, map_inv]; group⟩

/-- `N`-conjugacy is transitive. -/
theorem trans {s₁ s₂ s₃ : S.Splitting} (h₁ : S.IsConj s₁ s₂) (h₂ : S.IsConj s₂ s₃) :
    S.IsConj s₁ s₃ := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  exact ⟨n₁ * n₂, by simp only [hn₁, hn₂, map_mul]; group⟩

/-- The setoid of splittings with `N`-conjugacy -/
def setoid : Setoid S.Splitting where
  r := S.IsConj
  iseqv := {
    refl := refl S
    symm := symm S
    trans := trans S
  }

end IsConj

/-- The `N`-conjugacy classes of splittings -/
def ConjClasses (S : GroupExtension N E G) := Quotient <| IsConj.setoid S

end GroupExtension

namespace SemidirectProduct

variable {φ : G →* MulAut N} (s : (toGroupExtension φ).Splitting)

theorem right_sectionHom (g : G) : (s.sectionHom g).right = g := by
  rw [← rightHom_eq_right, ← toGroupExtension_rightHom, s.rightHom_sectionHom]

end SemidirectProduct
