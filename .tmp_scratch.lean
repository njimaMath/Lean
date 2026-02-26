import Mathlib
open scoped BigOperators ENNReal
namespace Scratch
variable {d : ℕ}
abbrev Zd (d : ℕ) : Type := Fin d → ℤ

def IsNN {d} (x y : Zd d) : Prop :=
  ∃ i : Fin d, (∀ j : Fin d, j ≠ i → x j = y j) ∧ (y i = x i + 1 ∨ y i = x i - 1)

def Weights (d : ℕ) : Type := Zd d → Zd d → ℝ≥0∞
structure SAPath (d : ℕ) where
  verts : List (Zd d)
  nonempty : verts ≠ []
  adj : verts.Chain' (IsNN (d := d))
  nodup : verts.Nodup
namespace SAPath
variable {d : ℕ}
def start (γ : SAPath d) : Zd d := γ.verts.head!
def finish (γ : SAPath d) : Zd d := γ.verts.getLast γ.nonempty
def edges (γ : SAPath d) : List (Zd d × Zd d) := γ.verts.zip γ.verts.tail
def time (w : Weights d) (γ : SAPath d) : ℝ≥0∞ := (γ.edges.map (fun e => w e.1 e.2)).sum
def Between (x y : Zd d) : Set (SAPath d) := {γ | γ.start = x ∧ γ.finish = y}
end SAPath

def passageTimeZd {d} (w : Weights d) (x y : Zd d) : ℝ≥0∞ :=
  sInf (Set.image (SAPath.time (d := d) w) (SAPath.Between (d := d) x y))

namespace FPP
variable {d : ℕ}
open SAPath

-- attempt proof skeleton
theorem test (w : Weights d) (x y z : Zd d) :
    passageTimeZd (d := d) w x z ≤ passageTimeZd (d := d) w x y + passageTimeZd (d := d) w y z := by
  classical
  -- abbreviate sets
  let Sxz : Set ℝ≥0∞ := Set.image (SAPath.time (d := d) w) (SAPath.Between (d := d) x z)
  let Sxy : Set ℝ≥0∞ := Set.image (SAPath.time (d := d) w) (SAPath.Between (d := d) x y)
  let Syz : Set ℝ≥0∞ := Set.image (SAPath.time (d := d) w) (SAPath.Between (d := d) y z)
  -- rewrite goal
  --
  -- TODO
  admit

end FPP
end Scratch
