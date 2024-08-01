import Mathlib.Algebra.Group.Subgroup.Basic

namespace Subgroup

/-- A subgroup of a commutative group is commutative. -/
@[to_additive "A subgroup of a commutative group is commutative."]
instance {G : Type*} [CommGroup G] (H : Subgroup G) : H.IsCommutative :=
  ⟨CommMagma.to_isCommutative⟩

@[to_additive]
lemma mul_comm_of_mem_isCommutative {G : Type*} [Group G] (H : Subgroup G) [H.IsCommutative]
    {a b : G} (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a := by
  simpa only [Submonoid.mk_mul_mk, Subtype.mk.injEq] using mul_comm (⟨a, ha⟩ : H) (⟨b, hb⟩ : H)

end Subgroup

namespace MonoidHom

@[to_additive]
instance range_isCommutative {G : Type*} [CommGroup G] {N : Type*} [Group N] (f : G →* N) :
    f.range.IsCommutative :=
  range_eq_map f ▸ Subgroup.map_isCommutative ⊤ f

end MonoidHom
