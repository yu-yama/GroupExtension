import GroupExtension.Abelian

namespace GroupExtension

variable {N G : Type} [CommGroup N] [Group G] [MulDistribMulAction G N]

namespace ofMulDistribMulAction

variable (S S' : ofMulDistribMulAction N G)
instance : Group S.E := S.GroupE
instance : Group S'.E := S'.GroupE

/-- The normalized 2-cocycle corresponding to the group extension -/
noncomputable def toNormalizedTwoCocycles :
    groupCohomology.normalizedTwoCocycles (Rep.ofMulDistribMulAction G N) where
  toTwoCocycles := S.toTwoCocycle
  map_one_one := by
    simp only [toTwoCocycle, map_one, mul_one, inv_one]
    rw [ofMul_eq_zero]
    apply S.extension.inl_injective
    simp only [map_one, Function.invFun_eq ⟨1, map_one S.extension.inl⟩]

end ofMulDistribMulAction

/-- A group given by an extension corresponding to a normalized 2-cocycle -/
@[ext]
structure middleOfNormalizedTwoCocycles
    (f : groupCohomology.normalizedTwoCocycles (Rep.ofMulDistribMulAction G N)) where
  left : N
  right : G

variable (f : groupCohomology.normalizedTwoCocycles (Rep.ofMulDistribMulAction G N))

namespace middleOfNormalizedTwoCocycles

variable {f}

instance : Mul (middleOfNormalizedTwoCocycles f) where
  mul e₁ e₂ := ⟨e₁.left * e₁.right • e₂.left * Additive.toMul (α := N)
    (f.toTwoCocycles.val ⟨e₁.right, e₂.right⟩), e₁.right * e₂.right⟩

theorem mul_def (e₁ e₂ : middleOfNormalizedTwoCocycles f) :
    e₁ * e₂ = ⟨e₁.left * e₁.right • e₂.left * Additive.toMul (α := N)
    (f.toTwoCocycles.val ⟨e₁.right, e₂.right⟩), e₁.right * e₂.right⟩ := rfl

@[simp]
theorem mul_left (e₁ e₂ : middleOfNormalizedTwoCocycles f) : (e₁ * e₂).left = e₁.left *
    e₁.right • e₂.left * Additive.toMul (α := N) (f.toTwoCocycles.val ⟨e₁.right, e₂.right⟩) := rfl

@[simp]
theorem mul_right (e₁ e₂ : middleOfNormalizedTwoCocycles f) :
    (e₁ * e₂).right = e₁.right * e₂.right := rfl

instance : One (middleOfNormalizedTwoCocycles f) where
  one := ⟨1, 1⟩

theorem one_def : (1 : middleOfNormalizedTwoCocycles f) = ⟨1, 1⟩ := rfl

@[simp]
theorem one_left : (1 : middleOfNormalizedTwoCocycles f).left = 1 := rfl

@[simp]
theorem one_right : (1 : middleOfNormalizedTwoCocycles f).right = 1 := rfl

instance : Inv (middleOfNormalizedTwoCocycles f) where
  inv e := ⟨(Additive.toMul (α := N) (f.toTwoCocycles.val ⟨e.right⁻¹, e.right⟩))⁻¹ *
      e.right⁻¹ • e.left⁻¹, e.right⁻¹⟩

theorem inv_def (e : middleOfNormalizedTwoCocycles f) :
    e⁻¹ = ⟨(Additive.toMul (α := N) (f.toTwoCocycles.val ⟨e.right⁻¹, e.right⟩))⁻¹ *
      e.right⁻¹ • e.left⁻¹, e.right⁻¹⟩ := rfl

@[simp]
theorem inv_left (e : middleOfNormalizedTwoCocycles f) :
    e⁻¹.left = (Additive.toMul (α := N) (f.toTwoCocycles.val ⟨e.right⁻¹, e.right⟩))⁻¹ *
      e.right⁻¹ • e.left⁻¹ := rfl

@[simp]
theorem inv_right (e : middleOfNormalizedTwoCocycles f) : e⁻¹.right = e.right⁻¹ := rfl

instance : Group (middleOfNormalizedTwoCocycles f) where
  mul_assoc := by
    intro ⟨n₁, g₁⟩ ⟨n₂, g₂⟩ ⟨n₃, g₃⟩
    ext
    ·
      simp only [mul_left, mul_right, smul_mul', mul_smul]
      rw [mul_assoc _ _ (g₁ • g₂ • n₃), mul_comm _ (g₁ • g₂ • n₃)]
      repeat rw [mul_assoc]
      rw [← toMul_add, add_comm, (groupCohomology.mem_twoCocycles_iff f.toTwoCocycles.val).mp
        f.toTwoCocycles.property g₁ g₂ g₃, toMul_add, Rep.ofMulDistribMulAction_ρ_apply_apply,
        toMul_ofMul]
    ·
      simp only [mul_right, mul_assoc]
  one_mul _ := by
    simp only [mul_def, one_left, one_right, one_smul, one_mul,
      groupCohomology.normalizedTwoCocycles_map_one_fst, toMul_zero, mul_one]
  mul_one _ := by
    simp only [mul_def, one_left, one_right, smul_one, mul_one,
      groupCohomology.normalizedTwoCocycles_map_one_snd, toMul_zero]
  inv_mul_cancel _ := by
    simp only [inv_def, mul_def, inv_mul_cancel, smul_inv', inv_mul_cancel_right, one_def]

def inl : N →* middleOfNormalizedTwoCocycles f where
  toFun n := ⟨n, 1⟩
  map_one' := rfl
  map_mul' _ _ := by simp only [mul_def, f.map_one_one, toMul_zero, mul_one, one_smul]

@[simp]
theorem left_inl (n : N) : (inl n : middleOfNormalizedTwoCocycles f).left = n := rfl

@[simp]
theorem right_inl (n : N) : (inl n : middleOfNormalizedTwoCocycles f).right = 1 := rfl

theorem mem_range_inl (e : middleOfNormalizedTwoCocycles f) : e ∈ inl.range ↔ e.right = 1 :=
  ⟨fun ⟨n, hn⟩ ↦ hn ▸ right_inl n, fun h ↦ ⟨e.left,
    middleOfNormalizedTwoCocycles.ext (left_inl e.left) (h ▸ right_inl e.left)⟩⟩

theorem inl_injective : Function.Injective (inl (f := f)) := fun _ _ h ↦ by
  simpa only [inl, MonoidHom.coe_mk, OneHom.coe_mk, mk.injEq, and_true] using h

def rightHom : middleOfNormalizedTwoCocycles f →* G where
  toFun := right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem rightHom_eq_right : (rightHom : middleOfNormalizedTwoCocycles f → G) = right := rfl

theorem rightHom_surjective : Function.Surjective (rightHom (f := f)) := fun g ↦ ⟨⟨1, g⟩, rfl⟩

theorem range_inl_eq_ker_rightHom : (inl (f := f)).range = (rightHom (f := f)).ker := by
  ext e
  rw [mem_range_inl, MonoidHom.mem_ker, rightHom_eq_right]

theorem smul_map_inv_eq_map_inv (g : G) :
    g • Additive.toMul (α := N) (f.toTwoCocycles.val (g⁻¹, g)) =
    Additive.toMul (α := N) (f.toTwoCocycles.val ⟨g, g⁻¹⟩) := by
  rw [← groupCohomology.normalizedTwoCocycles_ρ_map_inv_eq_map_inv,
    Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul]

theorem inl_smul_eq_conj_inl (g : G) (n n' : N) :
    (inl (g • n) : middleOfNormalizedTwoCocycles f) = ⟨n', g⟩ * inl n * ⟨n', g⟩⁻¹ := by
  simp only [left_inl, right_inl, mul_def, inv_def, mul_one, smul_mul', smul_inv_smul,
    mul_inv_cancel, toMul_zero, groupCohomology.normalizedTwoCocycles_map_one_snd, smul_inv',
    smul_map_inv_eq_map_inv, mul_assoc, inv_mul_cancel_comm_assoc, mul_inv_cancel_comm_assoc]
  ext <;> rfl

end middleOfNormalizedTwoCocycles

def extensionOfNormalizedTwoCocycles : GroupExtension N (middleOfNormalizedTwoCocycles f) G where
  inl := middleOfNormalizedTwoCocycles.inl
  rightHom := middleOfNormalizedTwoCocycles.rightHom
  inl_injective := middleOfNormalizedTwoCocycles.inl_injective
  range_inl_eq_ker_rightHom := middleOfNormalizedTwoCocycles.range_inl_eq_ker_rightHom
  rightHom_surjective := middleOfNormalizedTwoCocycles.rightHom_surjective

theorem extensionOfNormalizedTwoCocycles_inl :
    (extensionOfNormalizedTwoCocycles f).inl = middleOfNormalizedTwoCocycles.inl := rfl

theorem extensionOfNormalizedTwoCocycles_rightHom :
    (extensionOfNormalizedTwoCocycles f).rightHom = middleOfNormalizedTwoCocycles.rightHom := rfl

@[simp]
theorem extensionOfNormalizedTwoCocycles_right_sectionOneHom (g : G) :
    ((extensionOfNormalizedTwoCocycles f).sectionOneHom g).right = g := by
  rw [← middleOfNormalizedTwoCocycles.rightHom_eq_right,
    ← extensionOfNormalizedTwoCocycles_rightHom, rightHom_sectionOneHom]

theorem extensionOfNormalizedTwoCocycles_sectionOneHom (g : G) :
    (extensionOfNormalizedTwoCocycles f).sectionOneHom g =
    ⟨((extensionOfNormalizedTwoCocycles f).sectionOneHom g).left, g⟩ :=
  middleOfNormalizedTwoCocycles.ext rfl (extensionOfNormalizedTwoCocycles_right_sectionOneHom f g)

namespace ofMulDistribMulAction

def ofNormalizedTwoCocycles : ofMulDistribMulAction N G where
  E := middleOfNormalizedTwoCocycles f
  GroupE := inferInstance
  extension := extensionOfNormalizedTwoCocycles f
  smul_eq_inducedConjAct := by
    intro g n
    simp only [inducedConjAct, MonoidHom.coe_mk, OneHom.coe_mk]
    apply (extensionOfNormalizedTwoCocycles f).inl_injective
    rw [inl_conjAct_comm, extensionOfNormalizedTwoCocycles_inl,
      extensionOfNormalizedTwoCocycles_sectionOneHom,
      ← middleOfNormalizedTwoCocycles.inl_smul_eq_conj_inl]

def toNormalizedTwoCocycles_ofNormalizedTwoCocycles :
    toNormalizedTwoCocycles (ofNormalizedTwoCocycles f) = f := by
  unfold toNormalizedTwoCocycles ofNormalizedTwoCocycles toTwoCocycle
  congr
  ext ⟨g₁, g₂⟩
  dsimp
  apply Additive.toMul.injective
  apply (extensionOfNormalizedTwoCocycles f).inl_injective
  rw [toMul_ofMul,
    Function.invFun_eq <|
      (extensionOfNormalizedTwoCocycles f).sectionOneHom_mul_mul_mul_inv_mem_range g₁ g₂,
    extensionOfNormalizedTwoCocycles_inl]
  ext
  ·
    simp only [middleOfNormalizedTwoCocycles.left_inl, middleOfNormalizedTwoCocycles.mul_left,
    middleOfNormalizedTwoCocycles.mul_right, middleOfNormalizedTwoCocycles.inv_left,
    middleOfNormalizedTwoCocycles.inv_right, extensionOfNormalizedTwoCocycles_right_sectionOneHom,
    smul_mul', smul_inv_smul, smul_inv', middleOfNormalizedTwoCocycles.smul_map_inv_eq_map_inv]
    simp only [mul_assoc, inv_mul_cancel_comm_assoc]
    apply (extensionOfNormalizedTwoCocycles f).inl_injective
    simp only [map_mul]
    rw [(ofNormalizedTwoCocycles f).smul_eq_inducedConjAct]
    sorry
  ·
    simp only [middleOfNormalizedTwoCocycles.right_inl, middleOfNormalizedTwoCocycles.mul_right,
    middleOfNormalizedTwoCocycles.inv_right, extensionOfNormalizedTwoCocycles_right_sectionOneHom,
    mul_inv_cancel]

-- σ g₁ *
-- g₁ • σ g₂ *
-- Additive.toMul (f (g₁, g₂)) *
-- (Additive.toMul (f (g₁ * g₂, (g₁ * g₂)⁻¹)))⁻¹ *
-- (σ (g₁ * g₂))⁻¹ *
-- Additive.toMul (f (g₁ * g₂, (g₁ * g₂)⁻¹)) =
-- Additive.toMul (f (g₁, g₂))

end ofMulDistribMulAction

end GroupExtension
