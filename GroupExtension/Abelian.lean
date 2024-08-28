import GroupExtension.Basic
import GroupExtension.Deps.Quotient
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

section

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

namespace Section

variable {S}
variable (σ : S.Section)

/-- The action of `G` on `N` by conjugation, defined using a section. -/
noncomputable def inducedConjAct : G →* MulAut N where
  toFun g := S.conjAct (σ g)
  map_one' := by
    obtain ⟨n, hn⟩ : σ 1 ∈ S.inl.range :=
      by rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, rightHom_section]
    simp only [← hn, conjAct_inl]
  map_mul' g₁ g₂ := by
    ext n
    apply S.inl_injective
    simp only [MulAut.mul_apply, inl_conjAct_comm]
    obtain ⟨n', hn'⟩ := exists_section_mul' σ g₁ g₂
    rw [hn', mul_assoc _ (S.inl n'), ← S.inl.map_mul, mul_comm, map_mul]
    group

/-- The action of `G` on `N` is independent of the choice of a section. -/
theorem inducedConjAct_eq (σ' : S.Section) : σ.inducedConjAct = σ'.inducedConjAct := by
  ext1 g
  simp only [inducedConjAct, MonoidHom.coe_mk, OneHom.coe_mk]
  apply conjAct_eq_of_rightHom_eq
  simp only [rightHom_section]

end Section

/-- `G` acts on `N` by conjugation. -/
noncomputable def inducedConjAct : G →* MulAut N := Section.inducedConjAct S.rightHomSurjInv

end

section

variable (N G : Type) [CommGroup N] [Group G] [MulDistribMulAction G N]

/-- The type of group extensions with the same kernel, quotient, and action of quotient on kernel -/
structure ofMulDistribMulAction where
  E : Type*
  GroupE : Group E
  extension : GroupExtension N E G
  smul_eq_inducedConjAct {g : G} {n : N} : g • n = extension.inducedConjAct g n

structure ofMulDistribMulActionWithSection extends ofMulDistribMulAction N G where
  σ : extension.Section

variable {N G}

namespace ofMulDistribMulAction

variable (S S' : ofMulDistribMulAction N G)
instance : Group S.E := S.GroupE
instance : Group S'.E := S'.GroupE

/-- Two terms of `GroupExtension.ofMulDistribMulAction` are equivalent iff their extensions are -/
def Equiv := S.extension.Equiv S'.extension

variable (N G)

/-- The setoid on equivalence of extensions -/
def setoid : Setoid (ofMulDistribMulAction N G) where
  r S S' := Nonempty (S.Equiv S')
  iseqv := {
    refl := fun S ↦ ⟨GroupExtension.Equiv.refl S.extension⟩
    symm := fun ⟨equiv⟩ ↦ ⟨GroupExtension.Equiv.symm equiv⟩
    trans := fun ⟨equiv⟩ ⟨equiv'⟩ ↦ ⟨GroupExtension.Equiv.trans equiv equiv'⟩
  }

/-- The equivalence classes of group extensions with the same kernel and the same quotient -/
def EquivClasses := Quotient <| setoid N G

end ofMulDistribMulAction

namespace ofMulDistribMulActionWithSection

variable (S S' : ofMulDistribMulActionWithSection N G)
instance : Group S.E := S.GroupE
instance : Group S'.E := S'.GroupE

theorem smul_eq_inducedConjAct' {g : G} {n : N} : g • n = S.σ.inducedConjAct g n :=
  Section.inducedConjAct_eq _ S.σ ▸ S.smul_eq_inducedConjAct

-- TODO: rename either `Equiv` to disambiguate
/-- Two terms of `GroupExtension.ofMulDistribMulActionWithSection` are equivalent iff their
  extensions are equivalent and the sections commute with the same homomorphism -/
structure Equiv extends S.extension.Equiv S'.extension where
  section_comm : toMonoidHom ∘ S.σ = S'.σ

variable (N G)

/-- The setoid on equivalence of extensions and sections -/
instance setoid : Setoid (ofMulDistribMulActionWithSection N G) where
  r S S' := Nonempty (S.Equiv S')
  iseqv := {
    refl := fun S ↦ ⟨{
      GroupExtension.Equiv.refl S.extension with
      section_comm := by
        ext g
        simp only [GroupExtension.Equiv.refl, Function.comp_apply, MonoidHom.id_apply]
    }⟩
    symm := fun ⟨equiv⟩ ↦ ⟨{
      GroupExtension.Equiv.symm equiv.toEquiv with
      section_comm := by
        simp only [GroupExtension.Equiv.symm, MonoidHom.coe_coe, MulEquiv.symm_comp_eq,
          GroupExtension.Equiv.toMulEquiv_eq_toMonoidHom]
        exact equiv.section_comm.symm
    }⟩
    trans := fun ⟨equiv⟩ ⟨equiv'⟩ ↦ ⟨{
      GroupExtension.Equiv.trans equiv.toEquiv equiv'.toEquiv with
      section_comm := by
        simp only [GroupExtension.Equiv.trans, MonoidHom.coe_comp, Function.comp.assoc,
          equiv.section_comm, equiv'.section_comm]
    }⟩
  }

/-- The equivalence classes of group extensions with sections with the same kernel and the same
  quotient -/
def EquivClasses := Quotient <| setoid N G

variable {N G}

/-- The 2-cocycle corresponding to the group extension -/
noncomputable def toTwoCocycle :
    groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N) where
  val := fun (g₁, g₂) ↦ Additive.ofMul (α := N) <|
    Function.invFun S.extension.inl <| S.σ g₁ * S.σ g₂ * (S.σ (g₁ * g₂))⁻¹
  property := by
    rw [groupCohomology.mem_twoCocycles_iff]
    intro g₁ g₂ g₃
    dsimp
    repeat rw [← ofMul_mul]
    rw [Equiv.apply_eq_iff_eq Additive.ofMul]
    apply S.extension.inl_injective
    rw [S.smul_eq_inducedConjAct', Section.inducedConjAct]
    simp only [map_mul, inl_conjAct_comm, MonoidHom.coe_mk, OneHom.coe_mk]
    repeat rw [Function.invFun_eq <| S.extension.section_mul_mul_mul_inv_mem_range _ _ _]
    rw [Subgroup.mul_comm_of_mem_isCommutative _
      (S.extension.section_mul_mul_mul_inv_mem_range _ _ _)
      (S.extension.section_mul_mul_mul_inv_mem_range _ _ _)]
    group

theorem inl_toTwoCocycle (g₁ g₂ : G) :
    S.extension.inl (Additive.toMul (α := N) (S.toTwoCocycle.val (g₁, g₂))) =
    S.σ g₁ * S.σ g₂ * (S.σ (g₁ * g₂))⁻¹ := by
  simp only [toTwoCocycle, toMul_ofMul,
    Function.invFun_eq <| S.extension.section_mul_mul_mul_inv_mem_range S.σ g₁ g₂]

end ofMulDistribMulActionWithSection

/-- The group given by an extension corresponding to a 2-cocycle -/
@[ext]
structure middleOfTwoCocycle (f : groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N)) where
  left : N
  right : G

variable (f : groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N))

namespace middleOfTwoCocycle

variable {f}

instance : Mul (middleOfTwoCocycle f) where
  mul e₁ e₂ := ⟨e₁.left * e₁.right • e₂.left * Additive.toMul (α := N) (f.val (e₁.right, e₂.right)),
    e₁.right * e₂.right⟩

theorem mul_def (e₁ e₂ : middleOfTwoCocycle f) :
    e₁ * e₂ = ⟨e₁.left * e₁.right • e₂.left * Additive.toMul (α := N) (f.val (e₁.right, e₂.right)),
    e₁.right * e₂.right⟩ := rfl

@[simp]
theorem mul_left (e₁ e₂ : middleOfTwoCocycle f) : (e₁ * e₂).left =
  e₁.left * e₁.right • e₂.left * Additive.toMul (α := N) (f.val (e₁.right, e₂.right)) := rfl

@[simp]
theorem mul_right (e₁ e₂ : middleOfTwoCocycle f) : (e₁ * e₂).right = e₁.right * e₂.right := rfl

instance : One (middleOfTwoCocycle f) where
  one := ⟨(Additive.toMul <| f.val (1, 1))⁻¹, 1⟩

theorem one_def : (1 : middleOfTwoCocycle f) = ⟨(Additive.toMul <| f.val (1, 1))⁻¹, 1⟩ := rfl

@[simp]
theorem one_left : (1 : middleOfTwoCocycle f).left = (Additive.toMul <| f.val (1, 1) : N)⁻¹ := rfl

@[simp]
theorem one_right : (1 : middleOfTwoCocycle f).right = 1 := rfl

instance : Inv (middleOfTwoCocycle f) where
  inv e := ⟨(e.right⁻¹ • e.left * Additive.toMul (α := N) (f.val (e.right⁻¹, e.right)) *
    (Additive.toMul (α := N) (f.val (1, 1))))⁻¹, e.right⁻¹⟩

theorem inv_def (e : middleOfTwoCocycle f) :
    e⁻¹ = ⟨(e.right⁻¹ • e.left * Additive.toMul (α := N) (f.val (e.right⁻¹, e.right)) *
    (Additive.toMul (α := N) (f.val (1, 1))))⁻¹, e.right⁻¹⟩ := rfl

@[simp]
theorem inv_left (e : middleOfTwoCocycle f) :
    e⁻¹.left = (e.right⁻¹ • e.left * Additive.toMul (α := N) (f.val (e.right⁻¹, e.right)) *
    (Additive.toMul (α := N) (f.val (1, 1))))⁻¹ := rfl

@[simp]
theorem inv_right (e : middleOfTwoCocycle f) : e⁻¹.right = e.right⁻¹ := rfl

instance : Group (middleOfTwoCocycle f) where
  mul_assoc := by
    intro ⟨n₁, g₁⟩ ⟨n₂, g₂⟩ ⟨n₃, g₃⟩
    ext
    ·
      simp only [mul_left, mul_right, smul_mul', mul_smul]
      rw [mul_assoc _ _ (g₁ • g₂ • n₃), mul_comm _ (g₁ • g₂ • n₃)]
      repeat rw [mul_assoc]
      rw [← toMul_add, add_comm, (groupCohomology.mem_twoCocycles_iff f.val).mp f.property g₁ g₂ g₃,
        toMul_add, Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul]
    ·
      simp only [mul_right, mul_assoc]
  one_mul e := by
    simp only [mul_def, one_left, one_right, one_smul, one_mul,
      groupCohomology.twoCocycles_map_one_fst f e.right, inv_mul_cancel_comm]
  mul_one e := by
    simp only [mul_def, one_left, one_right, mul_one, smul_inv', toMul_ofMul, inv_mul_cancel_right,
      groupCohomology.twoCocycles_map_one_snd f e.right, Rep.ofMulDistribMulAction_ρ_apply_apply]
  inv_mul_cancel := by
    intro ⟨n, g⟩
    ext
    ·
      simp only [mul_left, inv_left, inv_right, one_left]
      group
    ·
      simp only [mul_right, inv_right, inv_mul_cancel, one_right]

def inl : N →* middleOfTwoCocycle f where
  toFun n := ⟨n * (Additive.toMul (α := N) (f.val (1, 1)))⁻¹, 1⟩
  map_one' := by
    simp only [one_mul, one_def]
  map_mul' n₁ n₂ := by
    ext
    ·
      simp only [mul_left, one_smul, mul_assoc, inv_mul_cancel, mul_one]
      rw [mul_comm n₂]
    ·
      simp only [one_left, mul_right, mul_one]

@[simp]
theorem left_inl (n : N) :
    (inl n : middleOfTwoCocycle f).left = n * (Additive.toMul (α := N) (f.val (1, 1)))⁻¹ := rfl

@[simp]
theorem right_inl (n : N) : (inl n : middleOfTwoCocycle f).right = 1 := rfl

theorem mem_range_inl (e : middleOfTwoCocycle f) : e ∈ inl.range ↔ e.right = 1 :=
  ⟨fun ⟨n, hn⟩ ↦ hn ▸ right_inl n, fun h ↦ ⟨e.left * Additive.toMul (α := N) (f.val (1, 1)),
    middleOfTwoCocycle.ext (by rw [left_inl, mul_inv_cancel_right]) (h ▸ right_inl _)⟩⟩

theorem inl_injective : Function.Injective (inl (f := f)) := fun _ _ h ↦ by
  simpa only [inl, MonoidHom.coe_mk, OneHom.coe_mk, mk.injEq, mul_left_inj, and_true] using h

def rightHom : middleOfTwoCocycle f →* G where
  toFun := right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem rightHom_eq_right : (rightHom : middleOfTwoCocycle f → G) = right := rfl

-- TODO: reimplement using `inr` as in `SemidirectProduct`?
theorem rightHom_surjective : Function.Surjective (rightHom (f := f)) := fun g ↦ ⟨⟨1, g⟩, rfl⟩

theorem range_inl_eq_ker_rightHom : (inl (f := f)).range = (rightHom (f := f)).ker := by
  ext e
  rw [mem_range_inl, MonoidHom.mem_ker, rightHom_eq_right]

theorem smul_map_inv_eq (g : G) : g • Additive.toMul (α := N) (f.val (g⁻¹, g)) =
    Additive.toMul (α := N) (f.val (1, 1)) * (Additive.toMul (α := N) (f.val (g, 1)))⁻¹ *
    Additive.toMul (α := N) (f.val (g, g⁻¹)) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_toMul, ← Rep.ofMulDistribMulAction_ρ_apply_apply]
  rw [← sub_eq_iff_eq_add, ← sub_eq_add_neg]
  exact groupCohomology.twoCocycles_ρ_map_inv_sub_map_inv f g

theorem map_one_snd (g : G) : Additive.toMul (α := N) (f.val (g, 1)) =
    g • Additive.toMul (α := N) (f.val (1, 1)) := by
  apply Additive.ofMul.injective
  rw [ofMul_toMul, ← Rep.ofMulDistribMulAction_ρ_apply_apply]
  exact groupCohomology.twoCocycles_map_one_snd f g

theorem inl_smul_eq_conj_inl (g : G) (n n' : N) :
    (inl (g • n) : middleOfTwoCocycle f) = ⟨n', g⟩ * inl n * ⟨n', g⟩⁻¹ := by
  simp only [mul_def, left_inl, right_inl, inv_def, mul_one, smul_mul', smul_inv', smul_inv_smul,
    mul_inv_rev, smul_map_inv_eq, inv_inv, groupCohomology.twoCocycles_map_one_snd f g,
    Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul]
  ext
  ·
    simp only [left_inl]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  ·
    simp only [right_inl, mul_inv_cancel]

end middleOfTwoCocycle

def extensionOfTwoCocycle : GroupExtension N (middleOfTwoCocycle f) G where
  inl := middleOfTwoCocycle.inl
  rightHom := middleOfTwoCocycle.rightHom
  inl_injective := middleOfTwoCocycle.inl_injective
  range_inl_eq_ker_rightHom := middleOfTwoCocycle.range_inl_eq_ker_rightHom
  rightHom_surjective := middleOfTwoCocycle.rightHom_surjective

theorem extensionOfTwoCocycle_inl :
    (extensionOfTwoCocycle f).inl = middleOfTwoCocycle.inl := rfl

theorem extensionOfTwoCocycle_rightHom :
    (extensionOfTwoCocycle f).rightHom = middleOfTwoCocycle.rightHom := rfl

def sectionOfTwoCocycle : (extensionOfTwoCocycle f).Section where
  toFun := fun g ↦ ⟨1, g⟩
  is_section := by
      intro _
      simp only [extensionOfTwoCocycle_rightHom, middleOfTwoCocycle.rightHom_eq_right]

namespace ofMulDistribMulActionWithSection

def ofTwoCocycle : ofMulDistribMulActionWithSection N G where
  E := middleOfTwoCocycle f
  GroupE := inferInstance
  extension := extensionOfTwoCocycle f
  σ := sectionOfTwoCocycle f
  smul_eq_inducedConjAct := by
    intro g n
    unfold inducedConjAct
    rw [Section.inducedConjAct_eq _ (sectionOfTwoCocycle f)]
    simp only [Section.inducedConjAct, MonoidHom.coe_mk, OneHom.coe_mk, sectionOfTwoCocycle]
    apply (extensionOfTwoCocycle f).inl_injective
    rw [inl_conjAct_comm, extensionOfTwoCocycle_inl, ← middleOfTwoCocycle.inl_smul_eq_conj_inl]
    rfl

def toTwoCocycle_ofTwoCocycle :
    toTwoCocycle (ofTwoCocycle f) = f := by
  unfold toTwoCocycle ofTwoCocycle
  ext ⟨g₁, g₂⟩
  simp only
  apply Additive.toMul.injective
  apply (extensionOfTwoCocycle f).inl_injective
  rw [toMul_ofMul,
    Function.invFun_eq <|
      (extensionOfTwoCocycle f).section_mul_mul_mul_inv_mem_range _ g₁ g₂,
    extensionOfTwoCocycle_inl]
  simp only [sectionOfTwoCocycle, middleOfTwoCocycle.mul_def, middleOfTwoCocycle.inv_left,
    middleOfTwoCocycle.inv_right, mul_inv, smul_mul', smul_inv', coe_section_mk, smul_one, mul_one,
    one_mul, inv_one, mul_inv_cancel, middleOfTwoCocycle.smul_map_inv_eq, inv_inv,
    middleOfTwoCocycle.map_one_snd (g₁ * g₂)]
  rw [mul_right_comm _ _ ((g₁ * g₂) • Additive.toMul (α := N) (f.val (1, 1)))⁻¹,
    mul_inv_cancel_right, mul_assoc, inv_mul_cancel_right]
  ext <;> simp only [middleOfTwoCocycle.left_inl, middleOfTwoCocycle.right_inl]

theorem toTwoCocycle_eq_of_equiv
    {S S' : ofMulDistribMulActionWithSection N G} (equiv : S.Equiv S') :
    toTwoCocycle S = toTwoCocycle S' := by
  ext ⟨g₁, g₂⟩
  apply (Additive.toMul (α := N)).injective
  apply S'.extension.inl_injective
  rw [inl_toTwoCocycle, ← equiv.inl_comm, MonoidHom.comp_apply, inl_toTwoCocycle]
  simp only [map_mul, map_inv, ← equiv.section_comm, Function.comp_apply]

def ofTwoCocycleToTwoCocycleEquiv (S : ofMulDistribMulActionWithSection N G) :
    (ofTwoCocycle (toTwoCocycle S)).Equiv S where
  toMonoidHom := {
    toFun := fun ⟨n, g⟩ ↦ S.extension.inl n * S.σ g
    map_one' := by
      rw [middleOfTwoCocycle.one_def]
      simp only [map_inv, inl_toTwoCocycle, mul_one, mul_inv_cancel_right, inv_mul_cancel]
    map_mul' := by
      intro ⟨n₁, g₁⟩ ⟨n₂, g₂⟩
      unfold ofTwoCocycle
      simp only [map_mul, inl_toTwoCocycle]
      rw [S.smul_eq_inducedConjAct', Section.inducedConjAct]
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, inl_conjAct_comm, ← mul_assoc,
        inv_mul_cancel_right]
  }
  inl_comm := by
    unfold ofTwoCocycle extensionOfTwoCocycle
    ext n
    simp only [MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, middleOfTwoCocycle.left_inl,
      middleOfTwoCocycle.right_inl, map_mul, map_inv, inl_toTwoCocycle, mul_one,
      mul_inv_cancel_right, inv_mul_cancel_right]
  rightHom_comm := by
    unfold ofTwoCocycle extensionOfTwoCocycle
    ext ⟨n, g⟩
    simp only [MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, rightHom_inl,
      rightHom_section, one_mul, middleOfTwoCocycle.rightHom]
  section_comm := by
    unfold ofTwoCocycle sectionOfTwoCocycle
    ext g
    simp only [Function.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, coe_section_mk, map_one,
      one_mul]

noncomputable def equivTwoCocycles :
    EquivClasses N G ≃ groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N) where
  toFun := Quotient.lift toTwoCocycle fun _ _ ⟨equiv⟩ ↦ toTwoCocycle_eq_of_equiv equiv
  invFun f := Quotient.mk (setoid N G) (ofTwoCocycle f)
  left_inv := by
    rintro ⟨S⟩
    rw [← Quotient.mk, Quotient.lift_mk (s := setoid N G), Quotient.eq (r := setoid N G)]
    exact ⟨ofTwoCocycleToTwoCocycleEquiv S⟩
  right_inv f := by rw [Quotient.lift_mk (s := setoid N G), toTwoCocycle_ofTwoCocycle]

end ofMulDistribMulActionWithSection

namespace ofMulDistribMulAction

theorem sub_mem_twoCoboundaries_of_equiv {S S' : ofMulDistribMulAction N G} (equiv : S.Equiv S')
    (σ : S.extension.Section) (σ' : S'.extension.Section) :
    ({ S with σ := σ } : ofMulDistribMulActionWithSection N G).toTwoCocycle -
    ({ S' with σ := σ' } : ofMulDistribMulActionWithSection N G).toTwoCocycle ∈
    groupCohomology.twoCoboundaries (Rep.ofMulDistribMulAction G N) := by
  sorry

noncomputable def toH2 (S : ofMulDistribMulAction N G) :
    groupCohomology.H2 (Rep.ofMulDistribMulAction G N) :=
  Quotient.mk _ (ofMulDistribMulActionWithSection.toTwoCocycle {
    S with σ := S.extension.rightHomSurjInv
  })

def ofH2 (f : groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N)) :
    EquivClasses N G :=
  Quotient.mk _ (ofMulDistribMulActionWithSection.ofTwoCocycle f).toofMulDistribMulAction

def equivOfSubMemTwoCoboundaries
    {f f' : groupCohomology.twoCocycles (Rep.ofMulDistribMulAction G N)}
    (h : f - f' ∈ groupCohomology.twoCoboundaries (Rep.ofMulDistribMulAction G N)) :
    (ofMulDistribMulActionWithSection.ofTwoCocycle f).toofMulDistribMulAction.Equiv
    (ofMulDistribMulActionWithSection.ofTwoCocycle f').toofMulDistribMulAction where
  toMonoidHom := sorry
  inl_comm := sorry
  rightHom_comm := sorry

noncomputable def equivH2 :
    EquivClasses N G ≃ groupCohomology.H2 (Rep.ofMulDistribMulAction G N) where
  toFun := Quotient.lift toH2 fun _ _ ⟨equiv⟩ ↦ (Quotient.eq (r := Submodule.quotientRel _)).mpr <|
    (Submodule.quotientRel_r_def _).mpr <| sub_mem_twoCoboundaries_of_equiv equiv _ _
  invFun := Quotient.lift ofH2 fun _ _ h ↦ (Quotient.eq (r := setoid N G)).mpr
    ⟨equivOfSubMemTwoCoboundaries ((Submodule.quotientRel_r_def _).mp h)⟩
  left_inv := by
    rintro ⟨S⟩
    unfold ofH2 toH2
    rw [← Quotient.mk, Quotient.lift_mk (s := setoid N G)]
    simp only [Quotient.lift_mk, Quotient.eq (r := setoid N G)]
    exact ⟨(ofMulDistribMulActionWithSection.ofTwoCocycleToTwoCocycleEquiv {
      toofMulDistribMulAction := S,
      σ := S.extension.rightHomSurjInv
    }).toEquiv⟩
  right_inv := by
    rintro ⟨S⟩
    unfold ofH2 toH2
    rw [← Quotient.mk]
    simp only [Quotient.lift_mk]
    rw [Quotient.eq (r := Submodule.quotientRel _)]
    sorry

end ofMulDistribMulAction

end

end GroupExtension
