import Mathlib
open scoped ENNReal
namespace Test
variable {α : Type} [CompleteLinearOrder α] [CanonicallyOrderedCommSemiring α]
variable (S T : Set α)
#check ENNReal.sInf_add
end Test
