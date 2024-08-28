import Mathlib.Data.Quot

namespace Quotient

variable {α β : Sort*}

theorem lift_apply [s : Setoid α] (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (q : Quotient s) :
    Quotient.lift f h q = f q.out := by simpa [out_eq] using lift_mk f h q.out

end Quotient
