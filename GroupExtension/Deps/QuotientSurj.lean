import Mathlib.Logic.Equiv.Defs

#check Quotient.congr

variable {α β : Sort*} {f : α → β} (hf : Function.Surjective f)
  {ra : Setoid α} {rb : Setoid β} (eq : ∀ a₁ a₂ : α, ra.r a₁ a₂ ↔ rb.r (f a₁) (f a₂))

noncomputable example : Quotient ra ≃ Quotient rb where
  toFun := Quot.map f fun a₁ a₂ ↦ (eq a₁ a₂).mp
  invFun := Quot.map (Function.surjInv hf) fun b₁ b₂ h ↦
    (Function.surjInv_eq hf b₁ ▸ Function.surjInv_eq hf b₂ ▸
      (eq (Function.surjInv hf b₁) (Function.surjInv hf b₂)).mpr) h
  left_inv := by
    rintro ⟨a⟩
    simp only [Quot.map]
    repeat rw [← Quotient.mk]
    have {a₁ a₂ : α} : (a₁ ≈ a₂) = (ra.r a₁ a₂) := rfl
    rw [Quotient.eq, this, eq, Function.surjInv_eq hf]
    exact Quotient.eq.mp rfl
  right_inv := by
    rintro ⟨a⟩
    simp only [Quot.map, Function.surjInv_eq]
