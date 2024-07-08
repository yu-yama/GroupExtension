import «GroupExtension».Defs
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

namespace GroupExtension

variable {N E G : Type*} [Group N] [Group E] [Group G]

namespace Equiv

variable {E' : Type*} [Group E'] {S : GroupExtension N E G} {S' : GroupExtension N E' G} (equiv : Equiv S S')

/-- Short exact sequences of equivalent group extensions commute -/
theorem comm : S.rightHom.comp S.inl = S'.rightHom.comp S'.inl := by
  rw [equiv.rightHom_comm, MonoidHom.comp_assoc, ← equiv.inl_comm]

/-- The four lemma (deriving injectivity) specialized for group extensions -/
theorem injective : Function.Injective equiv.toMonoidHom := by
  rw [injective_iff_map_eq_one]
  intro e he
  have he' := congrArg S'.rightHom he
  rw [S'.rightHom.map_one, ← MonoidHom.comp_apply, ← equiv.rightHom_comm, ← MonoidHom.mem_ker, ← S.range_inl_eq_ker_rightHom] at he'
  obtain ⟨n, rfl⟩ := he'
  rw [← MonoidHom.comp_apply, ← equiv.inl_comm, (injective_iff_map_eq_one' S'.inl).mp S'.inl_injective] at he
  rw [he, S.inl.map_one]

/-- The four lemma (deriving surjectivity) specialized for group extensions -/
theorem surjective : Function.Surjective equiv.toMonoidHom := by
  intro e'
  obtain ⟨e, he⟩ := S.rightHom_surjective (S'.rightHom e')
  symm at he
  rw [equiv.rightHom_comm, MonoidHom.comp_apply, MonoidHom.eq_iff, ← S'.range_inl_eq_ker_rightHom] at he
  obtain ⟨n, hn⟩ := he
  use e * S.inl n
  rw [MonoidHom.map_mul, ← MonoidHom.comp_apply, ← equiv.inl_comm, hn, mul_inv_cancel_left]

/-- The five lemma specialized for group extensions -/
theorem bijective : Function.Bijective equiv.toMonoidHom := ⟨equiv.injective, equiv.surjective⟩

/-- A homomorphism between equivalent group extensions is indeed an isomorphism -/
noncomputable def toMulEquiv : E ≃* E' := MulEquiv.ofBijective equiv.toMonoidHom equiv.bijective

end Equiv

namespace Splitting

variable {S : GroupExtension N E G} (s : Splitting S)

theorem rightHom_sectionHom {g : G} : S.rightHom (s.sectionHom g) = g := by
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

/-- A split group extension is equivalent to a group extension giving a semidirect product -/
def equiv_semidirectProduct : (SemidirectProduct.toGroupExtension s.conjAct).Equiv S where
  toMonoidHom := monoidHom_semidirectProduct s
  inl_comm := by
    ext n
    simp only [SemidirectProduct.toGroupExtension, MonoidHom.comp_apply, monoidHom_semidirectProduct, MonoidHom.coe_mk, OneHom.coe_mk, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, mul_one]
  rightHom_comm := by
    ext ⟨n, g⟩
    simp only [SemidirectProduct.toGroupExtension, MonoidHom.comp_apply, SemidirectProduct.rightHom_eq_right, monoidHom_semidirectProduct, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, rightHom_inl, rightHom_sectionHom, one_mul]

noncomputable def mulEquiv_semidirectProduct : N ⋊[s.conjAct] G ≃* E := s.equiv_semidirectProduct.toMulEquiv

-- example (s' : Splitting S) : s.conjAct = s'.conjAct := by
--   ext g n
--   simp only [conjAct, MonoidHom.comp_apply]
--   simp?
--   -- simp [MonoidHom.ofInjective_apply]
--   sorry

end Splitting

end GroupExtension

-- variable (A G : Type*) [Group A] [Group G] (B : Subgroup A) (H : Subgroup G)

-- example (h₁ : A ≃ G) (h₂ : B ≃ H) : A ⧸ B ≃ G ⧸ H := by
--   exact?
--   sorry

-- trying a constructive approach

-- variable (N E G : Type*) [Group N] [MulOneClass E] [Group G]
-- structure GroupExtension where
--   inl : N →* E
--   rightHom : E →* G
--   inl_injective : Function.Injective inl
--   exact : ∀ {e : E}, rightHom e = 1 ↔ e ∈ Set.range inl -- Multiplicative version of Function.Exact
--   rightHom_surjective : Function.Surjective rightHom

-- variable {N E G}

-- namespace SemidirectProduct

-- def toGroupExtension (φ : G →* MulAut N) : GroupExtension N (N ⋊[φ] G) G where
--   inl := inl
--   rightHom := rightHom
--   inl_injective := SemidirectProduct.inl_injective
--   exact := sorry
--   rightHom_surjective := SemidirectProduct.rightHom_surjective

-- end SemidirectProduct

-- namespace GroupExtension

-- instance (S : GroupExtension N E G) : Group E where
--   mul_assoc := sorry
--   one_mul := sorry
--   mul_one := sorry
--   inv := sorry
--   mul_left_inv := sorry

-- end GroupExtension
