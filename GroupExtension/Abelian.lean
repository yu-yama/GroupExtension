import GroupExtension.Basic
import GroupExtension.Deps.LowDegree
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

/-!
# Lemmas about extensions by Abelian groups

This file gives lemmas about group extensions `1 → N → E → G → 1` that hold when `N` is Abelian.

For the main definitions, see `GroupTheory/GroupExtension/Defs.lean`. For basic lemmas about general
group extensions, see `GroupTheory/GroupExtension/Basic.lean`.
-/

namespace SemidirectProduct

variable {N G : Type} [CommGroup N] [Group G] (φ : G →* MulAut N)

/-- The category of `ℤ`-linear `G`-representation with `φ` being the multiplicative action -/
noncomputable def toRep (φ : G →* MulAut N) : Rep ℤ G :=
  @Rep.ofMulDistribMulAction G N _ _ (MulDistribMulAction.compHom N φ)

/-- Turns a splitting into the corresponding 1-cocyle. -/
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

/-- Turns a 1-cocycle into the corresponding splitting. -/
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
    map_one, one_mul, inv_one, MulAut.one_apply, right_sectionHom, map_inv, div_eq_mul_inv,
    mul_right_comm]
  apply and_iff_left
  rw [← rightHom_eq_right, map_inv, rightHom_inl, inv_one, mul_one]

/-- A bijection between the `N`-conjugacy classes of splittings and `H1` -/
def conjClasses_equiv_h1 : (toGroupExtension φ).ConjClasses ≃ groupCohomology.H1 (toRep φ) :=
  Quotient.congr (splitting_equiv_oneCocycles φ) (by
    intro s₁ s₂
    rw [Submodule.quotientRel_r_def]
    exact isConj_iff_sub_mem_oneCoboundaries φ s₁ s₂
  )

end SemidirectProduct

namespace GroupExtension

variable {N E G : Type*} [CommGroup N] [Group E] [Group G] (S : GroupExtension N E G)

theorem conjAct_inl (n : N) : S.conjAct (S.inl n) = 1 := by
  ext _
  apply S.inl_injective
  rw [MulAut.one_apply, inl_conjAct_comm]
  simp only [← map_inv, ← map_mul, mul_inv_cancel_comm]

theorem inl_range_le_conjAct_ker : S.inl.range ≤ S.conjAct.ker :=
  fun _ ⟨n, hn⟩ ↦ hn ▸ S.conjAct_inl n

/-- Terms of `E` acts on `N` in the same way if their values by `rightHom` coincide. -/
theorem conjAct_eq_of_rightHom_eq {e e' : E} (h : S.rightHom e = S.rightHom e') :
    S.conjAct e = S.conjAct e' := by
  obtain ⟨_, rfl⟩ := S.rightHom_eq_iff_exists_inl_mul.mp h
  rw [map_mul, conjAct_inl, one_mul]

/-- `G` acts on `N` by conjugation. This action is well-defined as `N` is abelian. -/
noncomputable def conjActMap : G → MulAut N :=
  fun g ↦ S.conjAct <| S.sectionOneHom g

-- This definition is currently unused. Should we use `inducedConjAct` rather than considering any
-- `conjActMap`?
noncomputable def inducedConjAct : G →* MulAut N :=
  (QuotientGroup.lift S.inl.range S.conjAct S.inl_range_le_conjAct_ker).comp
    S.quotientRangeInlEquivRight.symm

end GroupExtension

namespace GroupExtension

variable (N G : Type) [CommGroup N] [Group G] [hAct : MulDistribMulAction G N]

/-- The type of group extensions with the same kernel, quotient, and action of quotient on kernel -/
structure ofMulDistribMulAction where
  E : Type*
  GroupE : Group E
  extension : GroupExtension N E G
  smul_eq_conjAct {g : G} {n : N} : g • n = extension.conjActMap g n

namespace ofMulDistribMulAction

variable {N G}
variable (S S' : ofMulDistribMulAction N G)
instance : Group S.E := S.GroupE
instance : Group S'.E := S'.GroupE

/-- Two terms of `GroupExtension.ofMulDistribMulAction` are equivalent iff their extensions are -/
def Equiv := S.extension.Equiv S'.extension

/-- The setoid on equivalence of extensions -/
def setoid : Setoid (ofMulDistribMulAction N G) where
  r S S' := Nonempty (S.Equiv S')
  iseqv := {
    refl := fun S ↦ ⟨GroupExtension.Equiv.refl S.extension⟩
    symm := fun ⟨equiv⟩ ↦ ⟨GroupExtension.Equiv.symm equiv⟩
    trans := fun ⟨equiv⟩ ⟨equiv'⟩ ↦ ⟨GroupExtension.Equiv.trans equiv equiv'⟩
  }

/-- The 2-cocycle corresponding to the group extension -/
noncomputable def toTwoCocycle :
    groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N) where
  val := fun ⟨g₁, g₂⟩ ↦ Additive.ofMul (α := N) <|
    Function.invFun S.extension.inl (S.extension.sectionOneHom g₁ * S.extension.sectionOneHom g₂ *
      (S.extension.sectionOneHom (g₁ * g₂))⁻¹)
  property := by
    rw [groupCohomology.mem_twoCocycles_iff]
    intro g₁ g₂ g₃
    dsimp
    repeat rw [← ofMul_mul]
    rw [Equiv.apply_eq_iff_eq Additive.ofMul]
    apply S.extension.inl_injective
    rw [S.smul_eq_conjAct, conjActMap]
    simp only [map_mul, inl_conjAct_comm,
      Function.invFun_eq <| S.extension.sectionOneHom_mul_mul_mul_inv_mem_range _ _]
    rw [Subgroup.mul_comm_of_mem_isCommutative _
      (S.extension.sectionOneHom_mul_mul_mul_inv_mem_range _ _)
      (S.extension.sectionOneHom_mul_mul_mul_inv_mem_range _ _)]
    group

/-- The group given by an extension corresponding to a 2-cocycle -/
@[ext]
structure middleOfTwoCocycle (f : groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N)) where
  left : N
  right : G

variable (f : groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N))

namespace middleOfTwoCocycle

instance : Mul (middleOfTwoCocycle f) where
  mul e₁ e₂ := ⟨e₁.left * e₁.right • e₂.left * (Additive.toMul (f.val ⟨e₁.right, e₂.right⟩) : N),
    e₁.right * e₂.right⟩

def mul_def (e₁ e₂ : middleOfTwoCocycle f) :
  e₁ * e₂ = ⟨e₁.left * e₁.right • e₂.left * (Additive.toMul (f.val ⟨e₁.right, e₂.right⟩) : N),
    e₁.right * e₂.right⟩ := rfl

instance : One (middleOfTwoCocycle f) where
  one := ⟨1, 1⟩

def one_def : (1 : middleOfTwoCocycle f) = ⟨1, 1⟩ := rfl

def one_left : (1 : middleOfTwoCocycle f).left = 1 := rfl

def one_right : (1 : middleOfTwoCocycle f).right = 1 := rfl

instance : Inv (middleOfTwoCocycle f) where
  inv := sorry

instance : Group (middleOfTwoCocycle f) where
  mul_assoc e₁ e₂ e₃ := sorry
  one_mul a := by
    simp only [mul_def, one_left, one_right, one_smul, one_mul]
    congr
    sorry
  mul_one a := by
    simp only [mul_def, one_left, one_right, smul_one, mul_one]
    congr
    sorry
  mul_left_inv := sorry

end middleOfTwoCocycle

instance extensionOfTwoCocycle : GroupExtension N (middleOfTwoCocycle f) G where
  inl := {
    toFun := fun n ↦ ⟨n, 1⟩
    map_one' := rfl
    map_mul' := sorry
  }
  rightHom := sorry
  inl_injective := sorry
  range_inl_eq_ker_rightHom := sorry
  rightHom_surjective := sorry

def ofTwoCocycle : ofMulDistribMulAction N G where
  E := middleOfTwoCocycle f
  GroupE := inferInstance
  extension := extensionOfTwoCocycle f
  smul_eq_conjAct := sorry

variable (N G)
theorem toTwoCocycle_surjective : Function.Surjective (@toTwoCocycle N G _ _ hAct) := by
  intro f
  sorry

end ofMulDistribMulAction

end GroupExtension
