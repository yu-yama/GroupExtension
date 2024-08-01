import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Monoid and Group Extensions

This file defines extensions of monoids and groups and their associated structures such as
splittings and equivalences.

## Main definitions

For monoids `N`, `E`, and `G`:

- `MonoidExtension N E G`: structure for extensions of `G` by `N` as short exact sequences
  `1 → N → E → G → 1`
- `MonoidExtension.Equiv S S'`: structure for equivalences of two extensions `S` and `S'` as
  specific homomorphisms `E → E'` such that the diagram below is commutative

```text
      ↗︎ E  ↘
1 → N   ↓    G → 1
      ↘︎ E' ↗︎️
```

- `MonoidExtension.Splitting S`: structure for splittings of an extension `S` of `G` by `N` as
  section homomorphisms `G → E`

For groups `N`, `E` and `G`:

- `MonoidExtension.conjAct S`: the action of `E` on `N` by conjugation
- `SemidirectProduct.toMonoidExtension φ`: the group extension associated to the semidirect product
  coming from `φ : G →* MulAut N`, `1 → N → N ⋊[φ] G → G → 1`

## TODO

If `N` is an abelian group,

- there is a bijection between `N`-conjugacy classes of
  `(SemidirectProduct.toMonoidExtension φ).Splitting` and `groupCohomology.H1`
  (which is available in `GroupTheory/MonoidExtension/Abelian.lean` to be added in a later PR).
- there is a bijection between equivalence classes of group extensions and `groupCohomology.H2`
  (which is also stated as a TODO in `RepresentationTheory/GroupCohomology/LowDegree.lean`).
-/

variable (N E G : Type*)

/-- `MonoidExtension N E G` is a short exact sequence of monoids `1 → N → E → G → 1`. -/
structure MonoidExtension [MulOneClass N] [MulOneClass E] [MulOneClass G] where
  /-- The inclusion homomorphism `N →* E` -/
  inl : N →* E
  /-- The projection homomorphism `E →* G` -/
  rightHom : E →* G
  /-- The inclusion map is injective. -/
  inl_injective : Function.Injective inl
  /-- The range of the inclusion map is equal to the kernel of the projection map. -/
  mrange_inl_eq_mker_rightHom : MonoidHom.mrange inl = MonoidHom.mker rightHom
  /-- The projection map is surjective. -/
  rightHom_surjective : Function.Surjective rightHom

variable {N E G}

namespace MonoidExtension

variable [MulOneClass N] [MulOneClass E] [MulOneClass G] (S : MonoidExtension N E G)

@[simp]
theorem rightHom_inl (n : N) : S.rightHom (S.inl n) = 1 := by
  rw [← MonoidHom.mem_mker, ← S.mrange_inl_eq_mker_rightHom, MonoidHom.mem_mrange]
  exact exists_apply_eq_apply S.inl n

@[simp]
theorem rightHom_comp_inl : S.rightHom.comp S.inl = 1 := by
  ext n
  rw [MonoidHom.one_apply, MonoidHom.comp_apply]
  exact S.rightHom_inl n

/-- `MonoidExtension`s are equivalent iff there is a homomorphism making a commuting diagram. -/
structure Equiv {E' : Type*} [Group E'] (S' : MonoidExtension N E' G) where
  /-- The homomorphism -/
  toMonoidHom : E →* E'
  /-- The left-hand side of the diagram commutes. -/
  inl_comm : toMonoidHom.comp S.inl = S'.inl
  /-- The right-hand side of the diagram commutes. -/
  rightHom_comm : S'.rightHom.comp toMonoidHom = S.rightHom

/-- `Splitting` of a monoid extension is a section homomorphism. -/
structure Splitting where
  /-- A section homomorphism -/
  sectionHom : G →* E
  /-- The section is a left inverse of the projection map. -/
  rightHom_comp_sectionHom : S.rightHom.comp sectionHom = MonoidHom.id G

instance : FunLike (S.Splitting) G E where
  coe s := s.sectionHom
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

instance : MonoidHomClass (S.Splitting) G E where
  map_mul s := s.sectionHom.map_mul'
  map_one s := s.sectionHom.map_one'

end MonoidExtension

namespace MonoidExtension

variable [Group N] [Group E] [Group G] (S : MonoidExtension N E G)

theorem range_inl_eq_ker_rightHom : S.inl.range = S.rightHom.ker := by
  rw [← Subgroup.toSubmonoid_eq]
  exact S.mrange_inl_eq_mker_rightHom

/-- The range of the inclusion map is a normal subgroup. -/
instance normal_inl_range : (S.inl.range).Normal :=
  S.range_inl_eq_ker_rightHom ▸ S.rightHom.normal_ker

-- TODO: does Mathlib have any definition to compose this homomorphism using more concisely?
/-- `E` acts on `N` by conjugation. -/
noncomputable def conjAct : E →* MulAut N where
  toFun e := (MonoidHom.ofInjective S.inl_injective).trans <|
    (MulAut.conjNormal e).trans (MonoidHom.ofInjective S.inl_injective).symm
  map_one' := by
    ext _
    simp only [map_one, MulEquiv.trans_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  map_mul' _ _ := by
    ext _
    simp only [map_mul, MulEquiv.trans_apply, MulAut.mul_apply, MulEquiv.apply_symm_apply]

/-- The inclusion and a conjugation commute. -/
theorem inl_conjAct_comm {e : E} {n : N} : S.inl (S.conjAct e n) = e * S.inl n * e⁻¹ := by
  simp only [conjAct, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm]
  rfl

/- TODO: `IsConj` only requires `[MulOneClass N] [DivInvMonoid E] [MulOneClass G]`, but I am not
  sure whether relaxing the assumptions would be meaningful. -/
/-- A splitting of an extension `S` is `N`-conjugate to another iff there exists `n : N` such that
the section homomorphism is a conjugate of the other section homomorphism by `S.inl n`. -/
def IsConj (S : MonoidExtension N E G) (s s' : S.Splitting) : Prop :=
  ∃ n : N, s.sectionHom = fun g ↦ S.inl n * s'.sectionHom g * (S.inl n)⁻¹

end MonoidExtension

namespace SemidirectProduct

variable [Group N] [Group G] (φ : G →* MulAut N)

/-- The group extension associated to the semidirect product -/
def toMonoidExtension : MonoidExtension N (N ⋊[φ] G) G where
  inl_injective := inl_injective
  mrange_inl_eq_mker_rightHom := by
    simpa [← Subgroup.toSubmonoid_eq] using range_inl_eq_ker_rightHom
  rightHom_surjective := rightHom_surjective

theorem toMonoidExtension_inl : (toMonoidExtension φ).inl = SemidirectProduct.inl := rfl

theorem toMonoidExtension_rightHom : (toMonoidExtension φ).rightHom = SemidirectProduct.rightHom :=
  rfl

/-- A canonical splitting -/
def inr_splitting : (toMonoidExtension φ).Splitting where
  sectionHom := inr
  rightHom_comp_sectionHom := rightHom_comp_inr

end SemidirectProduct
