import Disjoint_paths.Lemmas.InwardAlternating
import Disjoint_paths.Lemmas.PathJoin

/-!
# A self-avoiding continuation through a short outer coordinate

The initial segment uses a third coordinate as its outward partner.  Once the
private coordinate reaches zero, the path switches to a large reservoir.  The
third coordinate prevents the transition from revisiting the penultimate
inner-sphere vertex.
-/

namespace DisjointPaths

noncomputable section

def shortOuterFirst {d : ℕ} (y : LatticePoint d)
    (i : Fin d) (si : ℤ) (h : Fin d) (sh : ℤ)
    (hih : i ≠ h) (hsi : Int.natAbs si = 1)
    (hsh : Int.natAbs sh = 1) (a : ℕ) : LatticePath d :=
  inwardAlternatingPath y i si h sh hih hsi hsh a

def shortOuterSecond {d : ℕ} (y : LatticePoint d)
    (i : Fin d) (si : ℤ) (h : Fin d) (sh : ℤ)
    (p : Fin d) (sp : ℤ)
    (hih : i ≠ h) (hip : i ≠ p) (_hhp : h ≠ p)
    (hsi : Int.natAbs si = 1) (hsh : Int.natAbs sh = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ) : LatticePath d :=
  inwardAlternatingPath (shortOuterFirst y i si h sh hih hsi hsh a).finish
    p sp i (-si) (Ne.symm hip) hsp (by simpa) b

lemma shortOuter_join {d : ℕ} (y : LatticePoint d)
    (i : Fin d) (si : ℤ) (h : Fin d) (sh : ℤ)
    (p : Fin d) (sp : ℤ)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (hsi : Int.natAbs si = 1) (hsh : Int.natAbs sh = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ) :
    (shortOuterFirst y i si h sh hih hsi hsh a).finish =
      (shortOuterSecond y i si h sh p sp hih hip hhp hsi hsh hsp a b).start := by
  simp [shortOuterSecond]

lemma shortOuterFirst_finish_private_zero {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ) (h : Fin d) (sh : ℤ)
    (hih : i ≠ h) (hsi : Int.natAbs si = 1)
    (hsh : Int.natAbs sh = 1) (a : ℕ)
  (hprivate : si * y i = a) :
    si * (shortOuterFirst y i si h sh hih hsi hsh a).finish i = 0 := by
  rw [shortOuterFirst, LatticePath.finish_inwardAlternatingPath]
  have hsq := sq_eq_one_of_natAbs_eq_one si hsi
  simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
    signedBasis_of_ne hih]
  simp only [add_zero]
  calc
    si * (y i - (a : ℤ) * si) = si * y i - (a : ℤ) * (si * si) := by ring
    _ = 0 := by rw [hsq, hprivate]; ring

lemma shortOuter_common_vertices {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ)
    (h : Fin d) (sh : ℤ) (p : Fin d) (sp : ℤ)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (hsi : Int.natAbs si = 1) (hsh : Int.natAbs sh = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (ha : 0 < a) (hprivate : si * y i = a) :
    ∀ x,
      x ∈ (shortOuterFirst y i si h sh hih hsi hsh a).vertices →
      x ∈ (shortOuterSecond y i si h sh p sp hih hip hhp hsi hsh hsp a b).vertices →
      x = (shortOuterFirst y i si h sh hih hsi hsh a).finish := by
  intro x hxfirst hxsecond
  have hfirst := (LatticePath.mem_vertices_alternatingPath_iff
    y i (-si) h (-sh) hih (by simpa) (by simpa) a x).mp (by
      simpa [shortOuterFirst, inwardAlternatingPath] using hxfirst)
  let z := (shortOuterFirst y i si h sh hih hsi hsh a).finish
  have hsecond := (LatticePath.mem_vertices_alternatingPath_iff
    z p (-sp) i si (Ne.symm hip) (by simpa) (by simpa) b x).mp (by
      simpa [shortOuterSecond, inwardAlternatingPath, z] using hxsecond)
  rcases hfirst with ⟨k, hk, hkx⟩
  rcases hsecond with ⟨l, hl, hlx⟩
  have hzi : si * z i = 0 := by
    exact shortOuterFirst_finish_private_zero y i si h sh hih hsi hsh a hprivate
  have hik := inwardAlternatingVertex_private_coordinate
    y i si h sh hih hsi k
  rw [hkx] at hik
  have hil : -si * (alternatingVertex z p (-sp) i si l) i =
      -si * z i + l / 2 := by
    simpa only [neg_neg] using inwardAlternatingVertex_reservoir_coordinate
      z p sp i (-si) (Ne.symm hip) (by simpa using hsi) l
  rw [hlx] at hil
  have hzi' : -si * z i = 0 := by linarith
  have hdiv : (l : ℤ) / 2 = ((l / 2 : ℕ) : ℤ) := by omega
  have hsx : si * x i = -((l / 2 : ℕ) : ℤ) := by
    calc
      si * x i = -(-si * x i) := by ring
      _ = -(-si * z i + l / 2) := by rw [hil]
      _ = -((l / 2 : ℕ) : ℤ) := by rw [hzi', hdiv]; ring
  have hkhalf : (k + 1) / 2 ≤ a := by omega
  have hkzero : (k + 1) / 2 = a := by omega
  have hlzero : l / 2 = 0 := by omega
  have hkcases : k = 2 * a - 1 ∨ k = 2 * a := by omega
  have hlcases : l = 0 ∨ l = 1 := by omega
  have hzh : sh * z h = sh * y h + a := by
    dsimp [z]
    rw [shortOuterFirst, LatticePath.finish_inwardAlternatingPath]
    have hsq := sq_eq_one_of_natAbs_eq_one sh hsh
    simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
      signedBasis_of_ne (Ne.symm hih)]
    simp only [sub_zero]
    calc
      sh * (y h + (a : ℤ) * sh) = sh * y h + (a : ℤ) * (sh * sh) := by ring
      _ = sh * y h + a := by rw [hsq]; ring
  rcases hkcases with hkodd | hkeven
  · have hhfirst := inwardAlternatingVertex_reservoir_coordinate
      y i si h sh hih hsh k
    rw [hkx, hkodd] at hhfirst
    have hhsecond : x h = z h := by
      rw [← hlx]
      exact alternatingVertex_apply_of_ne z p (-sp) i si l h
        hhp (Ne.symm hih)
    have hhsigned : sh * x h = sh * z h := by rw [hhsecond]
    omega
  · rcases hlcases with hlzero | hlone
    · rw [← hkx, hkeven]
      simp [shortOuterFirst, inwardAlternatingPath, alternatingVertex_even]
    · have hpfirst : x p = y p := by
        rw [← hkx]
        exact alternatingVertex_apply_of_ne y i (-si) h (-sh) k p
          (Ne.symm hip) (Ne.symm hhp)
      have hzp : z p = y p := by
        dsimp [z]
        rw [shortOuterFirst, LatticePath.finish_inwardAlternatingPath]
        simp only [Pi.add_apply, Pi.sub_apply,
          signedBasis_of_ne (Ne.symm hip), signedBasis_of_ne (Ne.symm hhp),
          sub_zero, add_zero]
      have hpsecond : sp * (alternatingVertex z p (-sp) i si l) p =
          sp * z p - (l + 1) / 2 := by
        simpa only [neg_neg] using inwardAlternatingVertex_private_coordinate
          z p sp i (-si) (Ne.symm hip) hsp l
      rw [hlx, hlone] at hpsecond
      have hpsigned : sp * x p = sp * z p - 1 := by
        simpa using hpsecond
      rw [hpfirst, hzp] at hpsigned
      omega

def shortOuterPath {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ)
    (h : Fin d) (sh : ℤ) (p : Fin d) (sp : ℤ)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (hsi : Int.natAbs si = 1) (hsh : Int.natAbs sh = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (ha : 0 < a) (hprivate : si * y i = a) : LatticePath d :=
  LatticePath.join
    (shortOuterFirst y i si h sh hih hsi hsh a)
    (shortOuterSecond y i si h sh p sp hih hip hhp hsi hsh hsp a b)
    (shortOuter_join y i si h sh p sp hih hip hhp hsi hsh hsp a b)
    (shortOuter_common_vertices y i si h sh p sp hih hip hhp hsi hsh hsp a b
      ha hprivate)

@[simp] lemma start_shortOuterPath {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ)
    (h : Fin d) (sh : ℤ) (p : Fin d) (sp : ℤ)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (hsi : Int.natAbs si = 1) (hsh : Int.natAbs sh = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (ha : 0 < a) (hprivate : si * y i = a) :
    (shortOuterPath y i si h sh p sp hih hip hhp hsi hsh hsp a b ha hprivate).start = y := by
  simp [shortOuterPath, shortOuterFirst]

@[simp] lemma edgeLength_shortOuterPath {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ)
    (h : Fin d) (sh : ℤ) (p : Fin d) (sp : ℤ)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (hsi : Int.natAbs si = 1) (hsh : Int.natAbs sh = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (ha : 0 < a) (hprivate : si * y i = a) :
    (shortOuterPath y i si h sh p sp hih hip hhp hsi hsh hsp a b ha hprivate).edgeLength =
      2 * a + 2 * b := by
  simp [shortOuterPath, shortOuterFirst, shortOuterSecond]

lemma edgeLength_shortOuterPath_of_le {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ)
    (h : Fin d) (sh : ℤ) (p : Fin d) (sp : ℤ)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (hsi : Int.natAbs si = 1) (hsh : Int.natAbs sh = 1)
    (hsp : Int.natAbs sp = 1) (a m : ℕ)
    (ha : 0 < a) (ham : a ≤ m) (hprivate : si * y i = a) :
    (shortOuterPath y i si h sh p sp hih hip hhp hsi hsh hsp a (m - a)
      ha hprivate).edgeLength = 2 * m := by
  rw [edgeLength_shortOuterPath]
  omega

lemma shortOuterPath_vertices_on_two_spheres {d n : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ)
    (h : Fin d) (sh : ℤ) (p : Fin d) (sp : ℤ)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (hsi : Int.natAbs si = 1) (hsh : Int.natAbs sh = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (ha : 0 < a) (hprivate : si * y i = a)
    (hy : y ∈ sphere d (n + 1)) (hhout : 0 ≤ sh * y h)
    (hpreservoir : (b : ℤ) ≤ sp * y p) :
    ∀ x ∈
      (shortOuterPath y i si h sh p sp hih hip hhp hsi hsh hsp a b ha hprivate).vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
  let first := shortOuterFirst y i si h sh hih hsi hsh a
  let z := first.finish
  let second := shortOuterSecond y i si h sh p sp hih hip hhp hsi hsh hsp a b
  have hfirstOuter : z ∈ sphere d (n + 1) := by
    change l1Norm first.finish = n + 1
    exact l1Norm_finish_inwardAlternatingPath y i si h sh hih hsi hsh a hy
      (le_of_eq hprivate.symm) hhout
  have hzp : z p = y p := by
    dsimp [z, first]
    rw [shortOuterFirst, LatticePath.finish_inwardAlternatingPath]
    simp only [Pi.add_apply, Pi.sub_apply,
      signedBasis_of_ne (Ne.symm hip), signedBasis_of_ne (Ne.symm hhp),
      sub_zero, add_zero]
  have hzi : si * z i = 0 := by
    dsimp [z, first]
    exact shortOuterFirst_finish_private_zero y i si h sh hih hsi hsh a hprivate
  have hfirstVertices : ∀ x ∈ first.vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
    dsimp [first]
    exact LatticePath.inwardAlternatingPath_vertices_on_two_spheres
      y i si h sh hih hsi hsh a hy (le_of_eq hprivate.symm) hhout
  have hsecondVertices : ∀ x ∈ second.vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
    dsimp [second]
    have hzneg : -si * z i = 0 := by linarith [hzi]
    exact LatticePath.inwardAlternatingPath_vertices_on_two_spheres
      z p sp i (-si) (Ne.symm hip) hsp (by simpa using hsi) b
      hfirstOuter (by simpa [hzp] using hpreservoir) (by simp [hzneg])
  intro x hx
  change x ∈ first.vertices ++ second.vertices.tail at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hfirstVertices x hx
  · exact hsecondVertices x (List.mem_of_mem_tail hx)

lemma shortOuterPath_finish_private_coordinate {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ)
    (h : Fin d) (sh : ℤ) (p : Fin d) (sp : ℤ)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (hsi : Int.natAbs si = 1) (hsh : Int.natAbs sh = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (ha : 0 < a) (hprivate : si * y i = a) :
    si *
      (shortOuterPath y i si h sh p sp hih hip hhp hsi hsh hsp a b ha hprivate).finish i =
      -(b : ℤ) := by
  let first := shortOuterFirst y i si h sh hih hsi hsh a
  let second := shortOuterSecond y i si h sh p sp hih hip hhp hsi hsh hsp a b
  let z := first.finish
  have hzi : si * z i = 0 := by
    dsimp [z, first]
    exact shortOuterFirst_finish_private_zero y i si h sh hih hsi hsh a hprivate
  have hfinish :
      (shortOuterPath y i si h sh p sp hih hip hhp hsi hsh hsp a b ha hprivate).finish =
        second.finish := by
    dsimp [second, first]
    simp [shortOuterPath]
  rw [hfinish]
  dsimp [second]
  rw [shortOuterSecond, LatticePath.finish_inwardAlternatingPath]
  have hsq := sq_eq_one_of_natAbs_eq_one si hsi
  simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
    signedBasis_of_ne hip]
  have hfirstZero : si * first.finish i = 0 := by
    simpa [z] using hzi
  calc
    si * (first.finish i - 0 + (b : ℤ) * -si) =
        si * first.finish i - (b : ℤ) * (si * si) := by ring
    _ = -(b : ℤ) := by rw [hfirstZero, hsq]; ring

lemma shortOuterPath_coordinate_bounds {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ)
    (h : Fin d) (sh : ℤ) (p : Fin d) (sp : ℤ)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (hsi : Int.natAbs si = 1) (hsh : Int.natAbs sh = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (ha : 0 < a) (hprivate : si * y i = a)
    (x : LatticePoint d)
    (hx : x ∈ (shortOuterPath y i si h sh p sp hih hip hhp hsi hsh hsp a b
      ha hprivate).vertices) (r : Fin d) :
    y r - (a + b : ℕ) ≤ x r ∧ x r ≤ y r + (a + b : ℕ) := by
  let first := shortOuterFirst y i si h sh hih hsi hsh a
  let second := shortOuterSecond y i si h sh p sp hih hip hhp hsi hsh hsp a b
  let z := first.finish
  have hfirstDisp : ∀ w ∈ first.vertices,
      Int.natAbs (w r - y r) ≤ a := by
    intro w hw
    dsimp [first] at hw ⊢
    exact LatticePath.inwardAlternatingPath_coordinate_displacement_le
      y i si h sh hih hsi hsh a w hw r
  have hsecondDisp : ∀ w ∈ second.vertices,
      Int.natAbs (w r - z r) ≤ b := by
    intro w hw
    dsimp [second, z, first] at hw ⊢
    exact LatticePath.inwardAlternatingPath_coordinate_displacement_le
      (shortOuterFirst y i si h sh hih hsi hsh a).finish
      p sp i (-si) (Ne.symm hip) hsp (by simpa using hsi) b w hw r
  change x ∈ first.vertices ++ second.vertices.tail at hx
  rcases List.mem_append.mp hx with hxfirst | hxsecond
  · have hdisp := hfirstDisp x hxfirst
    constructor
    · have hlower := coordinate_sub_le_of_natAbs_sub_le x y r a hdisp
      omega
    · have hupper := coordinate_le_add_of_natAbs_sub_le x y r a hdisp
      omega
  · have hxsecond' : x ∈ second.vertices := List.mem_of_mem_tail hxsecond
    have hdispFirst := hfirstDisp z (LatticePath.finish_mem_vertices first)
    have hdispSecond := hsecondDisp x hxsecond'
    have hfirstLower := coordinate_sub_le_of_natAbs_sub_le z y r a hdispFirst
    have hfirstUpper := coordinate_le_add_of_natAbs_sub_le z y r a hdispFirst
    have hsecondLower := coordinate_sub_le_of_natAbs_sub_le x z r b hdispSecond
    have hsecondUpper := coordinate_le_add_of_natAbs_sub_le x z r b hdispSecond
    constructor <;> omega

lemma shortOuterPath_private_coordinate_le_start {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ)
    (h : Fin d) (sh : ℤ) (p : Fin d) (sp : ℤ)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (hsi : Int.natAbs si = 1) (hsh : Int.natAbs sh = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (ha : 0 < a) (hprivate : si * y i = a)
    (x : LatticePoint d)
    (hx : x ∈ (shortOuterPath y i si h sh p sp hih hip hhp hsi hsh hsp a b
      ha hprivate).vertices) :
    si * x i ≤ si * y i := by
  let first := shortOuterFirst y i si h sh hih hsi hsh a
  let second := shortOuterSecond y i si h sh p sp hih hip hhp hsi hsh hsp a b
  let z := first.finish
  have hfirst : ∀ w ∈ first.vertices, si * w i ≤ si * y i := by
    intro w hw
    dsimp [first] at hw ⊢
    exact LatticePath.inwardAlternatingPath_private_coordinate_le_start
      y i si h sh hih hsi hsh a w hw
  have hsecond : ∀ w ∈ second.vertices, si * w i ≤ 0 := by
    intro w hw
    have hmem := (LatticePath.mem_vertices_alternatingPath_iff
      z p (-sp) i si (Ne.symm hip) (by simpa) (by simpa) b w).mp (by
        simpa [second, shortOuterSecond, inwardAlternatingPath, z] using hw)
    rcases hmem with ⟨k, hk, hkw⟩
    have hcoord : -si * alternatingVertex z p (-sp) i si k i =
        -si * z i + k / 2 := by
      simpa only [neg_neg] using inwardAlternatingVertex_reservoir_coordinate
        z p sp i (-si) (Ne.symm hip) (by simpa using hsi) k
    rw [hkw] at hcoord
    have hzi : si * z i = 0 := by
      dsimp [z, first]
      exact shortOuterFirst_finish_private_zero y i si h sh hih hsi hsh a hprivate
    have hdiv : (0 : ℤ) ≤ k / 2 := by positivity
    linarith
  change x ∈ first.vertices ++ second.vertices.tail at hx
  rcases List.mem_append.mp hx with hxfirst | hxsecond
  · exact hfirst x hxfirst
  · have hzero := hsecond x (List.mem_of_mem_tail hxsecond)
    have hstart : 0 ≤ si * y i := by rw [hprivate]; positivity
    linarith

lemma shortOuterPath_eq_start_of_private_coordinate_eq {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ)
    (h : Fin d) (sh : ℤ) (p : Fin d) (sp : ℤ)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (hsi : Int.natAbs si = 1) (hsh : Int.natAbs sh = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (ha : 0 < a) (hprivate : si * y i = a)
    (x : LatticePoint d)
    (hx : x ∈ (shortOuterPath y i si h sh p sp hih hip hhp hsi hsh hsp
      a b ha hprivate).vertices)
    (heq : si * x i = si * y i) :
    x = y := by
  let first := shortOuterFirst y i si h sh hih hsi hsh a
  let second := shortOuterSecond y i si h sh p sp hih hip hhp hsi hsh hsp a b
  let z := first.finish
  change x ∈ first.vertices ++ second.vertices.tail at hx
  rcases List.mem_append.mp hx with hxfirst | hxsecond
  · rcases (LatticePath.mem_vertices_alternatingPath_iff
      y i (-si) h (-sh) hih (by simpa) (by simpa) a x).mp (by
        simpa [first, shortOuterFirst, inwardAlternatingPath] using hxfirst) with
      ⟨k, -, hkx⟩
    have hcoord := inwardAlternatingVertex_private_coordinate
      y i si h sh hih hsi k
    rw [hkx, heq] at hcoord
    have hkzero : k = 0 := by omega
    subst k
    have hzero : alternatingVertex y i (-si) h (-sh) 0 = y := by
      funext r
      simp [alternatingVertex, signedBasis]
    exact hkx.symm.trans hzero
  · have hxsecond' : x ∈ second.vertices := List.mem_of_mem_tail hxsecond
    rcases (LatticePath.mem_vertices_alternatingPath_iff
      z p (-sp) i si (Ne.symm hip) (by simpa) (by simpa) b x).mp (by
        simpa [second, shortOuterSecond, inwardAlternatingPath, z] using hxsecond') with
      ⟨k, -, hkx⟩
    have hzi : si * z i = 0 := by
      dsimp [z, first]
      exact shortOuterFirst_finish_private_zero y i si h sh hih hsi hsh a hprivate
    have hcoord : -si * (alternatingVertex z p (-sp) i si k) i =
        -si * z i + k / 2 := by
      simpa only [neg_neg] using inwardAlternatingVertex_reservoir_coordinate
        z p sp i (-si) (Ne.symm hip) (by simpa using hsi) k
    rw [hkx] at hcoord
    have hnonneg : (0 : ℤ) ≤ k / 2 := by positivity
    have hxnonpos : si * x i ≤ 0 := by linarith
    have hstartpos : 0 < si * y i := by rw [hprivate]; positivity
    linarith

lemma shortOuterPath_other_coordinate_ge_start {d : ℕ}
    (y : LatticePoint d) (i h p : Fin d)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (a b : ℕ) (ha : 0 < a)
    (hprivate : coordinateSign (y i) * y i = a)
    (x : LatticePoint d)
    (hx : x ∈ (shortOuterPath y i (coordinateSign (y i)) h
      (coordinateSign (y h)) p (coordinateSign (y p)) hih hip hhp
      (natAbs_coordinateSign _) (natAbs_coordinateSign _)
      (natAbs_coordinateSign _) a b ha hprivate).vertices)
    (r : Fin d) (hri : r ≠ i) (hrp : r ≠ p) :
    coordinateSign (y r) * y r ≤ coordinateSign (y r) * x r := by
  let first := shortOuterFirst y i (coordinateSign (y i)) h
    (coordinateSign (y h)) hih (natAbs_coordinateSign _)
    (natAbs_coordinateSign _) a
  let second := shortOuterSecond y i (coordinateSign (y i)) h
    (coordinateSign (y h)) p (coordinateSign (y p)) hih hip hhp
    (natAbs_coordinateSign _) (natAbs_coordinateSign _)
    (natAbs_coordinateSign _) a b
  let z := first.finish
  have hfirst : ∀ w ∈ first.vertices,
      coordinateSign (y r) * y r ≤ coordinateSign (y r) * w r := by
    intro w hw
    by_cases hrh : r = h
    · subst r
      exact LatticePath.inwardAlternatingPath_reservoir_coordinate_ge_start
        y i (coordinateSign (y i)) h (coordinateSign (y h)) hih
        (natAbs_coordinateSign _) (natAbs_coordinateSign _) a w (by
          simpa [first, shortOuterFirst] using hw)
    · have hcoord := LatticePath.inwardAlternatingPath_other_coordinate
        y i (coordinateSign (y i)) h (coordinateSign (y h)) hih
        (natAbs_coordinateSign _) (natAbs_coordinateSign _) a w (by
          simpa [first, shortOuterFirst] using hw) r hri hrh
      rw [hcoord]
  change x ∈ first.vertices ++ second.vertices.tail at hx
  rcases List.mem_append.mp hx with hxfirst | hxsecond
  · exact hfirst x hxfirst
  · have hxsecond' : x ∈ second.vertices := List.mem_of_mem_tail hxsecond
    have hcoord : x r = z r := by
      exact LatticePath.inwardAlternatingPath_other_coordinate
        z p (coordinateSign (y p)) i (-coordinateSign (y i)) (Ne.symm hip)
        (natAbs_coordinateSign _) (by simpa using natAbs_coordinateSign (y i))
        b x (by simpa [second, shortOuterSecond, z] using hxsecond')
        r hrp hri
    rw [hcoord]
    exact hfirst z (LatticePath.finish_mem_vertices first)

lemma shortOuterPath_other_coordinate_le_finish {d : ℕ}
    (y : LatticePoint d) (i h p : Fin d)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (a b : ℕ) (ha : 0 < a)
    (hprivate : coordinateSign (y i) * y i = a)
    (x : LatticePoint d)
    (hx : x ∈ (shortOuterPath y i (coordinateSign (y i)) h
      (coordinateSign (y h)) p (coordinateSign (y p)) hih hip hhp
      (natAbs_coordinateSign _) (natAbs_coordinateSign _)
      (natAbs_coordinateSign _) a b ha hprivate).vertices)
    (r : Fin d) (hri : r ≠ i) (hrp : r ≠ p) :
    coordinateSign (y r) * x r ≤ coordinateSign (y r) *
      (shortOuterPath y i (coordinateSign (y i)) h
        (coordinateSign (y h)) p (coordinateSign (y p)) hih hip hhp
        (natAbs_coordinateSign _) (natAbs_coordinateSign _)
        (natAbs_coordinateSign _) a b ha hprivate).finish r := by
  let first := shortOuterFirst y i (coordinateSign (y i)) h
    (coordinateSign (y h)) hih (natAbs_coordinateSign _)
    (natAbs_coordinateSign _) a
  let second := shortOuterSecond y i (coordinateSign (y i)) h
    (coordinateSign (y h)) p (coordinateSign (y p)) hih hip hhp
    (natAbs_coordinateSign _) (natAbs_coordinateSign _)
    (natAbs_coordinateSign _) a b
  let z := first.finish
  have hfinish :
      (shortOuterPath y i (coordinateSign (y i)) h
        (coordinateSign (y h)) p (coordinateSign (y p)) hih hip hhp
        (natAbs_coordinateSign _) (natAbs_coordinateSign _)
        (natAbs_coordinateSign _) a b ha hprivate).finish = second.finish := by
    simp [shortOuterPath, first, second]
  have hsecondCoord : second.finish r = z r := by
    exact LatticePath.inwardAlternatingPath_other_coordinate
      z p (coordinateSign (y p)) i (-coordinateSign (y i)) (Ne.symm hip)
      (natAbs_coordinateSign _) (by simpa using natAbs_coordinateSign (y i))
      b second.finish (LatticePath.finish_mem_vertices _) r hrp hri
  have hfirst : ∀ w ∈ first.vertices,
      coordinateSign (y r) * w r ≤ coordinateSign (y r) * z r := by
    intro w hw
    by_cases hrh : r = h
    · subst r
      rcases (LatticePath.mem_vertices_alternatingPath_iff
        y i (-coordinateSign (y i)) h (-coordinateSign (y h)) hih
        (by simpa using natAbs_coordinateSign (y i))
        (by simpa using natAbs_coordinateSign (y h)) a w).mp
        (by simpa [first, shortOuterFirst, inwardAlternatingPath] using hw) with
        ⟨k, hk, hkw⟩
      have hwcoord := inwardAlternatingVertex_reservoir_coordinate
        y i (coordinateSign (y i)) h (coordinateSign (y h)) hih
        (natAbs_coordinateSign _) k
      rw [hkw] at hwcoord
      have hzcoord := inwardAlternatingVertex_reservoir_coordinate
        y i (coordinateSign (y i)) h (coordinateSign (y h)) hih
        (natAbs_coordinateSign _) (2 * a)
      have hzvertex : z = alternatingVertex y i (-coordinateSign (y i))
          h (-coordinateSign (y h)) (2 * a) := by
        simp [z, first, shortOuterFirst, inwardAlternatingPath,
          LatticePath.finish_alternatingPath, alternatingVertex_even]
      rw [← hzvertex] at hzcoord
      omega
    · have hwcoord := LatticePath.inwardAlternatingPath_other_coordinate
        y i (coordinateSign (y i)) h (coordinateSign (y h)) hih
        (natAbs_coordinateSign _) (natAbs_coordinateSign _) a w
        (by simpa [first, shortOuterFirst] using hw) r hri hrh
      have hzcoord := LatticePath.inwardAlternatingPath_other_coordinate
        y i (coordinateSign (y i)) h (coordinateSign (y h)) hih
        (natAbs_coordinateSign _) (natAbs_coordinateSign _) a z
        (by exact LatticePath.finish_mem_vertices first) r hri hrh
      rw [hwcoord, hzcoord]
  change x ∈ first.vertices ++ second.vertices.tail at hx
  rw [hfinish, hsecondCoord]
  rcases List.mem_append.mp hx with hx | hx
  · exact hfirst x hx
  · have hxcoord := LatticePath.inwardAlternatingPath_other_coordinate
      z p (coordinateSign (y p)) i (-coordinateSign (y i)) (Ne.symm hip)
      (natAbs_coordinateSign _) (by simpa using natAbs_coordinateSign (y i))
      b x (List.mem_of_mem_tail hx) r hrp hri
    rw [hxcoord]

/-- A path from the outer sphere which uses `i` as a private coordinate.
For a long private coordinate it is the usual alternating path.  Otherwise it
first exhausts that coordinate using `h`, and then continues using `p`. -/
def outerPrivatePath {d : ℕ} (y : LatticePoint d)
    (i h p : Fin d) (m : ℕ)
    (hyi : y i ≠ 0) (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p) : LatticePath d :=
  let si := coordinateSign (y i)
  let sh := coordinateSign (y h)
  let sp := coordinateSign (y p)
  if _hm : m ≤ Int.natAbs (y i) then
    inwardAlternatingPath y i si p sp hip (natAbs_coordinateSign _) 
      (natAbs_coordinateSign _) m
  else
    shortOuterPath y i si h sh p sp hih hip hhp
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) (natAbs_coordinateSign _)
      (Int.natAbs (y i)) (m - Int.natAbs (y i))
      (Int.natAbs_pos.mpr hyi) (coordinateSign_mul_self _)

@[simp] lemma start_outerPrivatePath {d : ℕ} (y : LatticePoint d)
    (i h p : Fin d) (m : ℕ)
    (hyi : y i ≠ 0) (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p) :
    (outerPrivatePath y i h p m hyi hih hip hhp).start = y := by
  unfold outerPrivatePath
  dsimp
  split_ifs <;> simp

@[simp] lemma edgeLength_outerPrivatePath {d : ℕ} (y : LatticePoint d)
    (i h p : Fin d) (m : ℕ)
    (hyi : y i ≠ 0) (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p) :
    (outerPrivatePath y i h p m hyi hih hip hhp).edgeLength = 2 * m := by
  unfold outerPrivatePath
  dsimp
  split_ifs with hm
  · simp
  · have ham : Int.natAbs (y i) ≤ m := by omega
    exact edgeLength_shortOuterPath_of_le y i (coordinateSign (y i)) h
      (coordinateSign (y h)) p (coordinateSign (y p)) hih hip hhp
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) (natAbs_coordinateSign _)
      (Int.natAbs (y i)) m (Int.natAbs_pos.mpr hyi) ham
      (coordinateSign_mul_self _)

lemma outerPrivatePath_vertices_on_two_spheres {d n : ℕ}
    (y : LatticePoint d) (i h p : Fin d) (m : ℕ)
    (hyi : y i ≠ 0) (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (hy : y ∈ sphere d (n + 1))
    (hreservoir : (m : ℤ) ≤ coordinateSign (y p) * y p) :
    ∀ x ∈ (outerPrivatePath y i h p m hyi hih hip hhp).vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
  unfold outerPrivatePath
  dsimp
  split_ifs with hm
  · have hinward : (m : ℤ) ≤ coordinateSign (y i) * y i := by
      rw [coordinateSign_mul_self]
      exact_mod_cast hm
    exact LatticePath.inwardAlternatingPath_vertices_on_two_spheres
      y i (coordinateSign (y i)) p (coordinateSign (y p)) hip
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) m hy
      hinward (by
        rw [coordinateSign_mul_self]
        positivity)
  · have ham : Int.natAbs (y i) ≤ m := by omega
    exact shortOuterPath_vertices_on_two_spheres y i (coordinateSign (y i)) h
      (coordinateSign (y h)) p (coordinateSign (y p)) hih hip hhp
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) (natAbs_coordinateSign _)
      (Int.natAbs (y i)) (m - Int.natAbs (y i)) (Int.natAbs_pos.mpr hyi)
      (coordinateSign_mul_self _) hy
      (by rw [coordinateSign_mul_self]; positivity) (by
        have : ((m - Int.natAbs (y i) : ℕ) : ℤ) ≤ (m : ℤ) := by
          exact_mod_cast Nat.sub_le _ _
        exact le_trans this hreservoir)

lemma outerPrivatePath_finish_private_coordinate {d : ℕ}
    (y : LatticePoint d) (i h p : Fin d) (m : ℕ)
    (hyi : y i ≠ 0) (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p) :
    coordinateSign (y i) *
      (outerPrivatePath y i h p m hyi hih hip hhp).finish i =
        (Int.natAbs (y i) : ℤ) - m := by
  unfold outerPrivatePath
  dsimp
  split_ifs with hm
  · rw [inwardAlternatingPath_finish_private_coordinate y i
      (coordinateSign (y i)) p (coordinateSign (y p)) hip
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) m,
      coordinateSign_mul_self]
  · have hprivate : coordinateSign (y i) * y i = Int.natAbs (y i) :=
      coordinateSign_mul_self _
    have ham : Int.natAbs (y i) ≤ m := by omega
    rw [shortOuterPath_finish_private_coordinate y i (coordinateSign (y i)) h
      (coordinateSign (y h)) p (coordinateSign (y p)) hih hip hhp
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) (natAbs_coordinateSign _)
      (Int.natAbs (y i)) (m - Int.natAbs (y i)) (Int.natAbs_pos.mpr hyi)
      hprivate]
    have hcast : ((m - Int.natAbs (y i) : ℕ) : ℤ) =
        (m : ℤ) - Int.natAbs (y i) := by
      omega
    rw [hcast]
    ring

lemma outerPrivatePath_coordinate_bounds {d : ℕ}
    (y : LatticePoint d) (i h p : Fin d) (m : ℕ)
    (hyi : y i ≠ 0) (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (x : LatticePoint d)
    (hx : x ∈ (outerPrivatePath y i h p m hyi hih hip hhp).vertices)
    (r : Fin d) :
    y r - m ≤ x r ∧ x r ≤ y r + m := by
  unfold outerPrivatePath at hx
  dsimp at hx
  split_ifs at hx with hm
  · have hdisp := LatticePath.inwardAlternatingPath_coordinate_displacement_le
      y i (coordinateSign (y i)) p (coordinateSign (y p)) hip
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) m x hx r
    exact ⟨coordinate_sub_le_of_natAbs_sub_le x y r m hdisp,
      coordinate_le_add_of_natAbs_sub_le x y r m hdisp⟩
  · have hbounds := shortOuterPath_coordinate_bounds y i (coordinateSign (y i)) h
      (coordinateSign (y h)) p (coordinateSign (y p)) hih hip hhp
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) (natAbs_coordinateSign _)
      (Int.natAbs (y i)) (m - Int.natAbs (y i)) (Int.natAbs_pos.mpr hyi)
      (coordinateSign_mul_self _) x hx r
    have ham : Int.natAbs (y i) ≤ m := by omega
    constructor <;> omega

lemma outerPrivatePath_private_coordinate_le_start {d : ℕ}
    (y : LatticePoint d) (i h p : Fin d) (m : ℕ)
    (hyi : y i ≠ 0) (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (x : LatticePoint d)
    (hx : x ∈ (outerPrivatePath y i h p m hyi hih hip hhp).vertices) :
    coordinateSign (y i) * x i ≤ coordinateSign (y i) * y i := by
  unfold outerPrivatePath at hx
  dsimp at hx
  split_ifs at hx with hm
  · exact LatticePath.inwardAlternatingPath_private_coordinate_le_start
      y i (coordinateSign (y i)) p (coordinateSign (y p)) hip
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) m x hx
  · exact shortOuterPath_private_coordinate_le_start y i (coordinateSign (y i)) h
      (coordinateSign (y h)) p (coordinateSign (y p)) hih hip hhp
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) (natAbs_coordinateSign _)
      (Int.natAbs (y i)) (m - Int.natAbs (y i)) (Int.natAbs_pos.mpr hyi)
      (coordinateSign_mul_self _) x hx

lemma outerPrivatePath_eq_start_of_private_coordinate_eq {d : ℕ}
    (y : LatticePoint d) (i h p : Fin d) (m : ℕ)
    (hyi : y i ≠ 0) (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (x : LatticePoint d)
    (hx : x ∈ (outerPrivatePath y i h p m hyi hih hip hhp).vertices)
    (heq : coordinateSign (y i) * x i = coordinateSign (y i) * y i) :
    x = y := by
  unfold outerPrivatePath at hx
  dsimp at hx
  split_ifs at hx with hm
  · rcases (LatticePath.mem_vertices_alternatingPath_iff
      y i (-coordinateSign (y i)) p (-coordinateSign (y p)) hip
      (by simpa) (by simpa) m x).mp (by
        simpa [inwardAlternatingPath] using hx) with ⟨k, -, hkx⟩
    have hcoord := inwardAlternatingVertex_private_coordinate
      y i (coordinateSign (y i)) p (coordinateSign (y p)) hip
      (natAbs_coordinateSign _) k
    rw [hkx, heq] at hcoord
    have hkzero : k = 0 := by omega
    subst k
    have hzero : alternatingVertex y i (-coordinateSign (y i)) p
        (-coordinateSign (y p)) 0 = y := by
      funext r
      simp [alternatingVertex, signedBasis]
    exact hkx.symm.trans hzero
  · exact shortOuterPath_eq_start_of_private_coordinate_eq
      y i (coordinateSign (y i)) h (coordinateSign (y h)) p
      (coordinateSign (y p)) hih hip hhp (natAbs_coordinateSign _)
      (natAbs_coordinateSign _) (natAbs_coordinateSign _)
      (Int.natAbs (y i)) (m - Int.natAbs (y i)) (Int.natAbs_pos.mpr hyi)
      (coordinateSign_mul_self _) x hx heq

lemma outerPrivatePath_other_coordinate_ge_start {d : ℕ}
    (y : LatticePoint d) (i h p : Fin d) (m : ℕ)
    (hyi : y i ≠ 0) (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (x : LatticePoint d)
    (hx : x ∈ (outerPrivatePath y i h p m hyi hih hip hhp).vertices)
    (r : Fin d) (hri : r ≠ i) (hrp : r ≠ p) :
    coordinateSign (y r) * y r ≤ coordinateSign (y r) * x r := by
  unfold outerPrivatePath at hx
  dsimp at hx
  split_ifs at hx with hm
  · have hcoord := LatticePath.inwardAlternatingPath_other_coordinate
      y i (coordinateSign (y i)) p (coordinateSign (y p)) hip
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) m x hx r hri hrp
    rw [hcoord]
  · exact shortOuterPath_other_coordinate_ge_start y i h p hih hip hhp
      (Int.natAbs (y i)) (m - Int.natAbs (y i)) (Int.natAbs_pos.mpr hyi)
      (coordinateSign_mul_self _) x hx r hri hrp

lemma outerPrivatePath_other_coordinate_le_finish {d : ℕ}
    (y : LatticePoint d) (i h p : Fin d) (m : ℕ)
    (hyi : y i ≠ 0) (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (x : LatticePoint d)
    (hx : x ∈ (outerPrivatePath y i h p m hyi hih hip hhp).vertices)
    (r : Fin d) (hri : r ≠ i) (hrp : r ≠ p) :
    coordinateSign (y r) * x r ≤ coordinateSign (y r) *
      (outerPrivatePath y i h p m hyi hih hip hhp).finish r := by
  unfold outerPrivatePath at hx ⊢
  dsimp at hx ⊢
  split_ifs at hx ⊢ with hm
  · have hxcoord := LatticePath.inwardAlternatingPath_other_coordinate
      y i (coordinateSign (y i)) p (coordinateSign (y p)) hip
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) m x hx r hri hrp
    have hfinishcoord := LatticePath.inwardAlternatingPath_other_coordinate
      y i (coordinateSign (y i)) p (coordinateSign (y p)) hip
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) m
      (inwardAlternatingPath y i (coordinateSign (y i)) p
        (coordinateSign (y p)) hip (natAbs_coordinateSign _)
        (natAbs_coordinateSign _) m).finish
      (LatticePath.finish_mem_vertices _) r hri hrp
    rw [hxcoord, hfinishcoord]
  · exact shortOuterPath_other_coordinate_le_finish y i h p hih hip hhp
      (Int.natAbs (y i)) (m - Int.natAbs (y i)) (Int.natAbs_pos.mpr hyi)
      (coordinateSign_mul_self _) x hx r hri hrp

end

end DisjointPaths
