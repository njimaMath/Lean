import Mathlib
import percolation.PercolationZd

open scoped BigOperators
open scoped Topology

namespace FPP

noncomputable section

variable {d : (*@$\mathbb{N}$@*)}

/-- The vertex set `Z^d`, represented as functions `Fin d (*@$\rightarrow$@*) (*@$\mathbb{Z}$@*)`. -/
abbrev Zd (d : (*@$\mathbb{N}$@*)) : Type := Fin d (*@$\rightarrow$@*) (*@$\mathbb{Z}$@*)

/-- The ambient space `R^d`, represented as functions `Fin d (*@$\rightarrow$@*) (*@$\mathbb{R}$@*)`. -/
abbrev Rd (d : (*@$\mathbb{N}$@*)) : Type := Fin d (*@$\rightarrow$@*) (*@$\mathbb{R}$@*)

/-- Coordinatewise floor map `R^d (*@$\rightarrow$@*) Z^d`. -/
def floorZd (x : Rd d) : Zd d := fun i => Int.floor (x i)

/-- Nearest-neighbor relation on `Z^d`. -/
def IsNN (x y : Zd d) : Prop :=
  (*@$\exists$@*) i : Fin d, ((*@$\forall$@*) j : Fin d, j (*@$\neq$@*) i (*@$\rightarrow$@*) x j = y j) (*@$\wedge$@*) (y i = x i + 1 (*@$\vee$@*) y i = x i - 1)

/-- Edge weights on oriented pairs of vertices (no symmetry assumed). -/
abbrev Weights (d : (*@$\mathbb{N}$@*)) : Type := Zd d (*@$\rightarrow$@*) Zd d (*@$\rightarrow$@*) (*@$\mathbb{R}$@*)(*@$\geq$@*)0(*@$\infty$@*)

/-- A self-avoiding nearest-neighbor path in `Z^d`, encoded as a list of vertices.

`adj` says successive vertices are nearest-neighbors.
`nodup` says the vertex list is self-avoiding.
-/
structure SAPath (d : (*@$\mathbb{N}$@*)) where
  verts : List (Zd d)
  nonempty : verts (*@$\neq$@*) []
  adj : verts.Chain' (IsNN (d := d))
  nodup : verts.Nodup

namespace SAPath

variable {d : (*@$\mathbb{N}$@*)}

/-- Start vertex of a path. -/
def start ((*@$\gamma$@*) : SAPath d) : Zd d := (*@$\gamma$@*).verts.head!

/-- End vertex of a path. -/
def finish ((*@$\gamma$@*) : SAPath d) : Zd d := (*@$\gamma$@*).verts.getLast (*@$\gamma$@*).nonempty

/-- The oriented edge list of consecutive vertex pairs. -/
def edges ((*@$\gamma$@*) : SAPath d) : List (Zd d × Zd d) :=
  (*@$\gamma$@*).verts.zip (*@$\gamma$@*).verts.tail

/-- The number of edges in the path. -/
def edgeLength ((*@$\gamma$@*) : SAPath d) : (*@$\mathbb{N}$@*) := (*@$\gamma$@*).edges.length

/-- Passage time of a path for a given weight function. -/
def time (w : Weights d) ((*@$\gamma$@*) : SAPath d) : (*@$\mathbb{R}$@*)(*@$\geq$@*)0(*@$\infty$@*) :=
  ((*@$\gamma$@*).edges.map (fun e => w e.1 e.2)).sum

/-- The set of self-avoiding paths from `x` to `y`. -/
def Between (x y : Zd d) : Set (SAPath d) :=
  {(*@$\gamma$@*) | (*@$\gamma$@*).start = x (*@$\wedge$@*) (*@$\gamma$@*).finish = y}

end SAPath

/-- First-passage time on `Z^d`: infimum of passage times over self-avoiding paths. -/
def passageTimeZd (w : Weights d) (x y : Zd d) : (*@$\mathbb{R}$@*)(*@$\geq$@*)0(*@$\infty$@*) :=
  sInf (Set.image (SAPath.time (d := d) w) (SAPath.Between (d := d) x y))

/-- First-passage time on `R^d × R^d` defined by flooring coordinates. -/
def passageTimeRd (w : Weights d) (x y : Rd d) : (*@$\mathbb{R}$@*)(*@$\geq$@*)0(*@$\infty$@*) :=
  passageTimeZd (d := d) w (floorZd (d := d) x) (floorZd (d := d) y)

/-- Geodesics in `Z^d`: self-avoiding paths from `x` to `y` attaining the passage time. -/
def GeodesicsZd (w : Weights d) (x y : Zd d) : Set (SAPath d) :=
  {(*@$\gamma$@*) | (*@$\gamma$@*) (*@$\in$@*) SAPath.Between (d := d) x y (*@$\wedge$@*) SAPath.time (d := d) w (*@$\gamma$@*) = passageTimeZd (d := d) w x y}

/-- Geodesics in `R^d`, defined by flooring the endpoints. -/
def GeodesicsRd (w : Weights d) (x y : Rd d) : Set (SAPath d) :=
  GeodesicsZd (d := d) w (floorZd (d := d) x) (floorZd (d := d) y)

/-- Subadditivity of passage times on `Z^d`. -/
theorem passageTimeZd_subadditive (w : Weights d) (x y z : Zd d) :
    passageTimeZd (d := d) w x z (*@$\leq$@*) passageTimeZd (d := d) w x y + passageTimeZd (d := d) w y z := by
  sorry

/-- Subadditivity of passage times on `R^d` (via flooring). -/
theorem passageTimeRd_subadditive (w : Weights d) (x y z : Rd d) :
    passageTimeRd (d := d) w x z (*@$\leq$@*) passageTimeRd (d := d) w x y + passageTimeRd (d := d) w y z := by
  sorry

section Random

open MeasureTheory
open scoped BigOperators

variable {(*@$\Omega$@*) : Type*} [MeasurableSpace (*@$\Omega$@*)]
variable ((*@$\mathbb{P}$@*) : Measure (*@$\Omega$@*)) [ProbabilityTheory.IsProbabilityMeasure (*@$\mathbb{P}$@*)]

/-- A random environment: `(*@$\omega$@*) (*@$\mapsto$@*) weight function` on oriented edges. -/
abbrev Env (d : (*@$\mathbb{N}$@*)) ((*@$\Omega$@*) : Type*) : Type := (*@$\Omega$@*) (*@$\rightarrow$@*) Weights d

variable ((*@$\tau$@*) : Env d (*@$\Omega$@*))

/-- Placeholder for the usual i.i.d. assumptions on edge weights. -/
def IIDWeights : Prop := True

/-- Placeholder for stationarity under lattice translations. -/
def Stationary : Prop := True

/-- Placeholder for ergodicity under lattice translations. -/
def Ergodic : Prop := True

/-- The standard basis vector `e_i` in `Z^d`. -/
def stdBasis (i : Fin d) : Zd d := fun j => if j = i then (1 : (*@$\mathbb{Z}$@*)) else 0

/-- The weight of the oriented edge from `0` to `± e_i`.

We index the sign by `Bool`: `true` means `+e_i`, `false` means `-e_i`.
-/
def neighborWeight (w : Weights d) (i : Fin d) (sgn : Bool) : (*@$\mathbb{R}$@*)(*@$\geq$@*)0(*@$\infty$@*) :=
  if sgn then w 0 (stdBasis (d := d) i) else w 0 (-stdBasis (d := d) i)

/-- The minimum of the `2d` weights adjacent to the origin.

This is written as `sInf` of the range so it is defined for all `d`.
When `d (*@$\geq$@*) 1`, this agrees with the minimum over the `2d` neighbors.
-/
def minNeighborWeight (w : Weights d) : (*@$\mathbb{R}$@*)(*@$\geq$@*)0(*@$\infty$@*) :=
  sInf (Set.range (fun p : Fin d × Bool => neighborWeight (d := d) w p.1 p.2))

/-- The integrability hypothesis `E[min_{i=1..2d} (*@$\tau$@*)_i] < (*@$\infty$@*)`.

We encode it as finiteness of the `lintegral` of the minimum adjacent weight.
-/
def minNeighborIntegrable : Prop :=
  ((*@$\int$@*)(*@$^-$@*) (*@$\omega$@*), minNeighborWeight (d := d) ((*@$\tau$@*) (*@$\omega$@*)) (*@$\partial$@*)(*@$\mathbb{P}$@*)) < (*@$\top$@*)

/-- Random first-passage time on `Z^d`. -/
def Tzd (x y : Zd d) : (*@$\Omega$@*) (*@$\rightarrow$@*) (*@$\mathbb{R}$@*)(*@$\geq$@*)0(*@$\infty$@*) := fun (*@$\omega$@*) => passageTimeZd (d := d) ((*@$\tau$@*) (*@$\omega$@*)) x y

/-- Random first-passage time on `R^d` (via flooring). -/
def Trd (x y : Rd d) : (*@$\Omega$@*) (*@$\rightarrow$@*) (*@$\mathbb{R}$@*)(*@$\geq$@*)0(*@$\infty$@*) := fun (*@$\omega$@*) => passageTimeRd (d := d) ((*@$\tau$@*) (*@$\omega$@*)) x y

/-- Existence of a time constant under an integrability hypothesis.

This is a typical Kingman subadditive ergodic theorem conclusion.
The statement is given for the `R^d` version that uses flooring.
-/
theorem timeConstant_exists
    (hd : 1 (*@$\leq$@*) d)
    (hIID : IIDWeights (d := d) ((*@$\mathbb{P}$@*) := (*@$\mathbb{P}$@*)) (*@$\tau$@*))
    (hStat : Stationary (d := d) ((*@$\mathbb{P}$@*) := (*@$\mathbb{P}$@*)) (*@$\tau$@*))
    (hErg : Ergodic (d := d) ((*@$\mathbb{P}$@*) := (*@$\mathbb{P}$@*)) (*@$\tau$@*))
    (hmin : minNeighborIntegrable (d := d) ((*@$\mathbb{P}$@*) := (*@$\mathbb{P}$@*)) (*@$\tau$@*)) :
    (*@$\exists$@*) (*@$\mu$@*) : Rd d (*@$\rightarrow$@*) (*@$\mathbb{R}$@*), (*@$\forall$@*) x : Rd d,
      ((*@$\forall$@*)(*@$^m$@*) (*@$\omega$@*) (*@$\partial$@*)(*@$\mathbb{P}$@*), Tendsto (fun n : (*@$\mathbb{N}$@*) =>
          (Trd (d := d) ((*@$\mathbb{P}$@*) := (*@$\mathbb{P}$@*)) (*@$\tau$@*) 0 (n (*@$\bullet$@*) x) (*@$\omega$@*)).toReal / (n : (*@$\mathbb{R}$@*)))
        Filter.atTop ((*@$\mathcal{N}$@*) ((*@$\mu$@*) x))) := by
  sorry

/-- Event: there exists a self-avoiding path starting at `0` of edge-length `n`
with passage time strictly smaller than `c n`. -/
def FastPathEvent (n : (*@$\mathbb{N}$@*)) (c : (*@$\mathbb{R}$@*)) : Set (*@$\Omega$@*) :=
  {(*@$\omega$@*) | (*@$\exists$@*) (*@$\gamma$@*) : SAPath d,
      (*@$\gamma$@*).start = 0 (*@$\wedge$@*) (*@$\gamma$@*).edgeLength = n (*@$\wedge$@*) SAPath.time (d := d) ((*@$\tau$@*) (*@$\omega$@*)) (*@$\gamma$@*) < ENNReal.ofReal (c * n)}

/-- The percolation parameter `p0 := P( (*@$\tau$@*)(0,e(*@$_1$@*)) = 0 )` as a real number.

This uses a fixed coordinate `i0` built from `hd : 1 (*@$\leq$@*) d`.
-/
def pZero (hd : 1 (*@$\leq$@*) d) : (*@$\mathbb{R}$@*) :=
  let i0 : Fin d := (*@$\langle$@*)0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd(*@$\rangle$@*)
  ((*@$\mathbb{P}$@*) {(*@$\omega$@*) | ((*@$\tau$@*) (*@$\omega$@*)) 0 (stdBasis (d := d) i0) = 0}).toReal

/-- Exponential bound on the probability of very fast self-avoiding paths,
under the subcritical percolation condition `pZero < pcd d`.

The constant `pcd d` is assumed to be defined in `percolation/PercolationZd.lean`.
-/
theorem prob_fastPath_lt_exp
    (hd : 1 (*@$\leq$@*) d)
    (hIID : IIDWeights (d := d) ((*@$\mathbb{P}$@*) := (*@$\mathbb{P}$@*)) (*@$\tau$@*))
    (hsub : pZero (d := d) ((*@$\mathbb{P}$@*) := (*@$\mathbb{P}$@*)) (*@$\tau$@*) hd < pcd d) :
    (*@$\exists$@*) c : (*@$\mathbb{R}$@*), 0 < c (*@$\wedge$@*) (*@$\forall$@*) n : (*@$\mathbb{N}$@*),
      (*@$\mathbb{P}$@*) (FastPathEvent (d := d) ((*@$\mathbb{P}$@*) := (*@$\mathbb{P}$@*)) (*@$\tau$@*) n c) < ENNReal.ofReal (Real.exp (-c * n)) := by
  sorry

/-- Existence of geodesics as a consequence of an exponential fast-path bound.

The conclusion states that almost surely, for every pair of lattice points `x y`,
there is at least one geodesic from `x` to `y`.
-/
theorem geodesic_exists_of_fastPath_bound
    (hd : 1 (*@$\leq$@*) d)
    (hIID : IIDWeights (d := d) ((*@$\mathbb{P}$@*) := (*@$\mathbb{P}$@*)) (*@$\tau$@*))
    (hbound : (*@$\exists$@*) c : (*@$\mathbb{R}$@*), 0 < c (*@$\wedge$@*) (*@$\forall$@*) n : (*@$\mathbb{N}$@*),
      (*@$\mathbb{P}$@*) (FastPathEvent (d := d) ((*@$\mathbb{P}$@*) := (*@$\mathbb{P}$@*)) (*@$\tau$@*) n c) < ENNReal.ofReal (Real.exp (-c * n))) :
    (*@$\forall$@*)(*@$^m$@*) (*@$\omega$@*) (*@$\partial$@*)(*@$\mathbb{P}$@*), (*@$\forall$@*) x y : Zd d, (GeodesicsZd (d := d) ((*@$\tau$@*) (*@$\omega$@*)) x y).Nonempty := by
  sorry

end Random

end FPP
