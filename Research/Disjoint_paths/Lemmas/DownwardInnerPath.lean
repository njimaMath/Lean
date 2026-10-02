import Disjoint_paths.Lemmas.PathJoin
import Disjoint_paths.Lemmas.Fan
import Disjoint_paths.Lemmas.Separation

/-!
# Inner paths directed across a coordinate hyperplane

The first segment spends the separating coordinate until it reaches zero.
The remaining two segments use a large, different reservoir: the private
coordinate grows first, and the separating coordinate then continues with
the opposite sign.  The resulting path is self-avoiding and remains on the
two consecutive spheres.
-/

namespace DisjointPaths

noncomputable section

namespace LatticePath

private lemma downwardContinuation_private_ge_start {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (continueAlternatingPath z i si r (-sr) p sp
      hip hrp hsi (by simpa using hsr) hsp a b (Or.inl hir)).vertices) :
    si * z i ≤ si * x i := by
  rcases mem_vertices_continueAlternatingPath z i si r (-sr) p sp
      hip hrp hsi (by simpa using hsr) hsp a b (Or.inl hir) x hx with hx | hx
  · exact alternatingPath_private_coordinate_ge_start
      z i si p sp hip hsi hsp a x hx
  · have hfirst := alternatingPath_private_coordinate_ge_start
      z i si p sp hip hsi hsp a
      (alternatingPath z i si p sp hip hsi hsp a).finish
      (finish_mem_vertices _)
    have hcoord := alternatingPath_other_coordinate
      (alternatingPath z i si p sp hip hsi hsp a).finish
      r (-sr) p sp hrp (by simpa using hsr) hsp b x hx i hir hip
    rw [hcoord]
    exact hfirst

private lemma downwardContinuation_separator_le_start {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (t : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (continueAlternatingPath z i si r (-sr) p sp
      hip hrp hsi (by simpa using hsr) hsp t t (Or.inl hir)).vertices) :
    sr * x r ≤ sr * z r := by
  rcases mem_vertices_continueAlternatingPath z i si r (-sr) p sp
      hip hrp hsi (by simpa using hsr) hsp t t (Or.inl hir) x hx with hx | hx
  · have hcoord := alternatingPath_other_coordinate
      z i si p sp hip hsi hsp t x hx r (Ne.symm hir) hrp
    rw [hcoord]
  · have hge := alternatingPath_private_coordinate_ge_start
      (alternatingPath z i si p sp hip hsi hsp t).finish
      r (-sr) p sp hrp (by simpa using hsr) hsp t x hx
    have hcoord := alternatingPath_other_coordinate
      z i si p sp hip hsi hsp t
      (alternatingPath z i si p sp hip hsi hsp t).finish
      (finish_mem_vertices _) r (Ne.symm hir) hrp
    rw [hcoord] at hge
    nlinarith

lemma downwardInitial_continuation_common_vertices {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ) :
    let first := alternatingPath z i si r sr hir hsi hsr s
    let second := continueAlternatingPath first.finish i si r (-sr) p sp
      hip hrp hsi (by simpa using hsr) hsp t t (Or.inl hir)
    ∀ x, x ∈ first.vertices → x ∈ second.vertices → x = first.finish := by
  dsimp
  intro x hxFirst hxSecond
  let first := alternatingPath z i si r sr hir hsi hsr s
  have hprivate : si * x i = si * first.finish i := by
    exact le_antisymm
      (alternatingPath_private_coordinate_le_finish
        z i si r sr hir hsi hsr s x hxFirst)
      (downwardContinuation_private_ge_start first.finish i r p si sr sp
        hir hip hrp hsi hsr hsp t t x hxSecond)
  have hreservoir : sr * x r ≤ sr * first.finish r :=
    downwardContinuation_separator_le_start first.finish i r p si sr sp
      hir hip hrp hsi hsr hsp t x hxSecond
  exact alternatingPath_eq_finish_of_private_eq_of_reservoir_le
    z i si r sr hir hsi hsr s x hxFirst hprivate hreservoir

def shortDownwardInnerPath {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ) : LatticePath d :=
  let first := alternatingPath z i si r sr hir hsi hsr s
  let second := continueAlternatingPath first.finish i si r (-sr) p sp
    hip hrp hsi (by simpa using hsr) hsp t t (Or.inl hir)
  join first second (by
    exact (start_continueAlternatingPath first.finish i si r (-sr) p sp
      hip hrp hsi (by simpa using hsr) hsp t t (Or.inl hir)).symm)
    (downwardInitial_continuation_common_vertices z i r p si sr sp
      hir hip hrp hsi hsr hsp s t)

@[simp] lemma shortDownwardInnerPath_start {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ) :
    (shortDownwardInnerPath z i r p si sr sp hir hip hrp
      hsi hsr hsp s t).start = z := by
  simp [shortDownwardInnerPath]

@[simp] lemma shortDownwardInnerPath_edgeLength {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ) :
    (shortDownwardInnerPath z i r p si sr sp hir hip hrp
      hsi hsr hsp s t).edgeLength = 2 * s + 4 * t := by
  simp [shortDownwardInnerPath]
  omega

lemma mem_vertices_shortDownwardInnerPath {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ) (x : LatticePoint d)
    (hx : x ∈ (shortDownwardInnerPath z i r p si sr sp hir hip hrp
      hsi hsr hsp s t).vertices) :
    x ∈ (alternatingPath z i si r sr hir hsi hsr s).vertices ∨
      x ∈ (continueAlternatingPath
        (alternatingPath z i si r sr hir hsi hsr s).finish
        i si r (-sr) p sp hip hrp hsi (by simpa using hsr) hsp
        t t (Or.inl hir)).vertices := by
  change x ∈ (alternatingPath z i si r sr hir hsi hsr s).vertices ++
    (continueAlternatingPath
      (alternatingPath z i si r sr hir hsi hsr s).finish
      i si r (-sr) p sp hip hrp hsi (by simpa using hsr) hsp
      t t (Or.inl hir)).vertices.tail at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (List.mem_of_mem_tail hx)

lemma shortDownwardInnerPath_private_coordinate_ge_start {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ) (x : LatticePoint d)
    (hx : x ∈ (shortDownwardInnerPath z i r p si sr sp hir hip hrp
      hsi hsr hsp s t).vertices) :
    si * z i ≤ si * x i := by
  rcases mem_vertices_shortDownwardInnerPath z i r p si sr sp
      hir hip hrp hsi hsr hsp s t x hx with hx | hx
  · exact alternatingPath_private_coordinate_ge_start
      z i si r sr hir hsi hsr s x hx
  · have hfirst := alternatingPath_private_coordinate_ge_start
      z i si r sr hir hsi hsr s
      (alternatingPath z i si r sr hir hsi hsr s).finish
      (finish_mem_vertices _)
    exact hfirst.trans
      (downwardContinuation_private_ge_start
        (alternatingPath z i si r sr hir hsi hsr s).finish
        i r p si sr sp hir hip hrp hsi hsr hsp t t x hx)

lemma shortDownwardInnerPath_eq_start_of_private_coordinate_eq {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ) (hs : 0 < s)
    (x : LatticePoint d)
    (hx : x ∈ (shortDownwardInnerPath z i r p si sr sp hir hip hrp
      hsi hsr hsp s t).vertices)
    (heq : si * x i = si * z i) : x = z := by
  rcases mem_vertices_shortDownwardInnerPath z i r p si sr sp
      hir hip hrp hsi hsr hsp s t x hx with hx | hx
  · exact alternatingPath_eq_start_of_private_coordinate_eq
      z i si r sr hir hsi hsr s x hx heq
  · have hfirst := alternatingPath_private_coordinate_ge_start
      z i si r sr hir hsi hsr s
      (alternatingPath z i si r sr hir hsi hsr s).finish
      (finish_mem_vertices _)
    have hfinish : si *
        (alternatingPath z i si r sr hir hsi hsr s).finish i =
        si * z i + s := by
      rw [finish_alternatingPath]
      have hsisq := sq_eq_one_of_natAbs_eq_one si hsi
      simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
        signedBasis_of_ne hir]
      nlinarith
    have hsecond := downwardContinuation_private_ge_start
      (alternatingPath z i si r sr hir hsi hsr s).finish
      i r p si sr sp hir hip hrp hsi hsr hsp t t x hx
    rw [heq, hfinish] at hsecond
    omega

lemma shortDownwardInnerPath_separator_coordinate_le_start {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ) (x : LatticePoint d)
    (hx : x ∈ (shortDownwardInnerPath z i r p si sr sp hir hip hrp
      hsi hsr hsp s t).vertices) :
    sr * x r ≤ sr * z r := by
  rcases mem_vertices_shortDownwardInnerPath z i r p si sr sp
      hir hip hrp hsi hsr hsp s t x hx with hx | hx
  · exact alternatingPath_reservoir_coordinate_le_start
      z i si r sr hir hsi hsr s x hx
  · have hfirst := alternatingPath_reservoir_coordinate_le_start
      z i si r sr hir hsi hsr s
      (alternatingPath z i si r sr hir hsi hsr s).finish
      (finish_mem_vertices _)
    exact (downwardContinuation_separator_le_start
      (alternatingPath z i si r sr hir hsi hsr s).finish
      i r p si sr sp hir hip hrp hsi hsr hsp t x hx).trans hfirst

lemma shortDownwardInnerPath_finish_separator_le_coordinate {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ)
    (hseparator : sr * z r = s) (x : LatticePoint d)
    (hx : x ∈ (shortDownwardInnerPath z i r p si sr sp hir hip hrp
      hsi hsr hsp s t).vertices) :
    sr * (shortDownwardInnerPath z i r p si sr sp hir hip hrp
      hsi hsr hsp s t).finish r ≤ sr * x r := by
  have hfinish : sr *
      (shortDownwardInnerPath z i r p si sr sp hir hip hrp
        hsi hsr hsp s t).finish r = sr * z r - s - t := by
    simp only [shortDownwardInnerPath, finish_join,
      finish_continueAlternatingPath, finish_alternatingPath, Pi.add_apply,
      Pi.sub_apply, signedBasis_same, signedBasis_of_ne (Ne.symm hir),
      signedBasis_of_ne hrp]
    have hsrsq := sq_eq_one_of_natAbs_eq_one sr hsr
    nlinarith
  rcases mem_vertices_shortDownwardInnerPath z i r p si sr sp
      hir hip hrp hsi hsr hsp s t x hx with hx | hx
  · rcases (mem_vertices_alternatingPath_iff
      z i si r sr hir hsi hsr s x).mp hx with ⟨k, hk, hkx⟩
    have hkcoord := alternatingVertex_reservoir_coordinate
      z i si r sr hir hsr k
    rw [hkx] at hkcoord
    rw [hfinish, hseparator, hkcoord]
    omega
  · rcases mem_vertices_continueAlternatingPath
      (alternatingPath z i si r sr hir hsi hsr s).finish
      i si r (-sr) p sp hip hrp hsi (by simpa using hsr) hsp
      t t (Or.inl hir) x hx with hx | hx
    · have hxR := alternatingPath_other_coordinate
        (alternatingPath z i si r sr hir hsi hsr s).finish
        i si p sp hip hsi hsp t x hx r (Ne.symm hir) hrp
      have hfirstR : sr *
          (alternatingPath z i si r sr hir hsi hsr s).finish r = 0 := by
        rw [finish_alternatingPath]
        have hsrsq := sq_eq_one_of_natAbs_eq_one sr hsr
        simp only [Pi.add_apply, Pi.sub_apply,
          signedBasis_of_ne (Ne.symm hir), signedBasis_same]
        nlinarith
      rw [hfinish, hseparator, hxR, hfirstR]
      omega
    · have hle := alternatingPath_private_coordinate_le_finish
        (alternatingPath
          (alternatingPath z i si r sr hir hsi hsr s).finish
          i si p sp hip hsi hsp t).finish
        r (-sr) p sp hrp (by simpa using hsr) hsp t x hx
      have hfinal : sr *
          (alternatingPath
            (alternatingPath
              (alternatingPath z i si r sr hir hsi hsr s).finish
              i si p sp hip hsi hsp t).finish
            r (-sr) p sp hrp (by simpa using hsr) hsp t).finish r =
          sr * z r - s - t := by
        simp only [finish_alternatingPath, Pi.add_apply, Pi.sub_apply,
          signedBasis_same, signedBasis_of_ne (Ne.symm hir),
          signedBasis_of_ne hrp]
        have hsrsq := sq_eq_one_of_natAbs_eq_one sr hsr
        nlinarith
      have hresult : sr *
          (alternatingPath
            (alternatingPath
              (alternatingPath z i si r sr hir hsi hsr s).finish
              i si p sp hip hsi hsp t).finish
            r (-sr) p sp hrp (by simpa using hsr) hsp t).finish r ≤
          sr * x r := by nlinarith
      rw [hfinal] at hresult
      simpa [hfinish] using hresult

lemma shortDownwardInnerPath_finish_private_coordinate {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ) :
    si * (shortDownwardInnerPath z i r p si sr sp hir hip hrp
      hsi hsr hsp s t).finish i = si * z i + s + t := by
  simp only [shortDownwardInnerPath, finish_join,
    finish_continueAlternatingPath, finish_alternatingPath, Pi.add_apply,
    Pi.sub_apply, signedBasis_same, signedBasis_of_ne hir,
    signedBasis_of_ne hip]
  have hsisq := sq_eq_one_of_natAbs_eq_one si hsi
  nlinarith

lemma shortDownwardInnerPath_finish_separator_coordinate {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ) :
    sr * (shortDownwardInnerPath z i r p si sr sp hir hip hrp
      hsi hsr hsp s t).finish r = sr * z r - s - t := by
  simp only [shortDownwardInnerPath, finish_join,
    finish_continueAlternatingPath, finish_alternatingPath, Pi.add_apply,
    Pi.sub_apply, signedBasis_same, signedBasis_of_ne (Ne.symm hir),
    signedBasis_of_ne hrp]
  have hsrsq := sq_eq_one_of_natAbs_eq_one sr hsr
  nlinarith

lemma shortDownwardInnerPath_other_coordinate {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ) (x : LatticePoint d)
    (hx : x ∈ (shortDownwardInnerPath z i r p si sr sp hir hip hrp
      hsi hsr hsp s t).vertices)
    (k : Fin d) (hki : k ≠ i) (hkr : k ≠ r) (hkp : k ≠ p) :
    x k = z k := by
  rcases mem_vertices_shortDownwardInnerPath z i r p si sr sp
      hir hip hrp hsi hsr hsp s t x hx with hx | hx
  · exact alternatingPath_other_coordinate
      z i si r sr hir hsi hsr s x hx k hki hkr
  · rcases mem_vertices_continueAlternatingPath
      (alternatingPath z i si r sr hir hsi hsr s).finish
      i si r (-sr) p sp hip hrp hsi (by simpa using hsr) hsp
      t t (Or.inl hir) x hx with hx | hx
    · rw [alternatingPath_other_coordinate
          (alternatingPath z i si r sr hir hsi hsr s).finish
          i si p sp hip hsi hsp t x hx k hki hkp,
        alternatingPath_other_coordinate z i si r sr hir hsi hsr s
          (alternatingPath z i si r sr hir hsi hsr s).finish
          (finish_mem_vertices _) k hki hkr]
    · rw [alternatingPath_other_coordinate
          (alternatingPath
            (alternatingPath z i si r sr hir hsi hsr s).finish
            i si p sp hip hsi hsp t).finish
          r (-sr) p sp hrp (by simpa using hsr) hsp t x hx k hkr hkp,
        alternatingPath_other_coordinate
          (alternatingPath z i si r sr hir hsi hsr s).finish
          i si p sp hip hsi hsp t
          (alternatingPath
            (alternatingPath z i si r sr hir hsi hsr s).finish
            i si p sp hip hsi hsp t).finish
          (finish_mem_vertices _) k hki hkp,
        alternatingPath_other_coordinate z i si r sr hir hsi hsr s
          (alternatingPath z i si r sr hir hsi hsr s).finish
          (finish_mem_vertices _) k hki hkr]

lemma shortDownwardInnerPath_reservoir_coordinate_le_start {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ) (x : LatticePoint d)
    (hx : x ∈ (shortDownwardInnerPath z i r p si sr sp hir hip hrp
      hsi hsr hsp s t).vertices) :
    sp * x p ≤ sp * z p := by
  rcases mem_vertices_shortDownwardInnerPath z i r p si sr sp
      hir hip hrp hsi hsr hsp s t x hx with hx | hx
  · have hxcoord := alternatingPath_other_coordinate
      z i si r sr hir hsi hsr s x hx p (Ne.symm hip) (Ne.symm hrp)
    rw [hxcoord]
  · rcases mem_vertices_continueAlternatingPath
      (alternatingPath z i si r sr hir hsi hsr s).finish
      i si r (-sr) p sp hip hrp hsi (by simpa using hsr) hsp
      t t (Or.inl hir) x hx with hx | hx
    · have hle := alternatingPath_reservoir_coordinate_le_start
        (alternatingPath z i si r sr hir hsi hsr s).finish
        i si p sp hip hsi hsp t x hx
      have hfirstP := alternatingPath_other_coordinate
        z i si r sr hir hsi hsr s
        (alternatingPath z i si r sr hir hsi hsr s).finish
        (finish_mem_vertices _) p (Ne.symm hip) (Ne.symm hrp)
      rw [hfirstP] at hle
      exact hle
    · have hle := alternatingPath_reservoir_coordinate_le_start
        (alternatingPath
          (alternatingPath z i si r sr hir hsi hsr s).finish
          i si p sp hip hsi hsp t).finish
        r (-sr) p sp hrp (by simpa using hsr) hsp t x hx
      have hmiddle := alternatingPath_reservoir_coordinate_le_start
        (alternatingPath z i si r sr hir hsi hsr s).finish
        i si p sp hip hsi hsp t
        (alternatingPath
          (alternatingPath z i si r sr hir hsi hsr s).finish
          i si p sp hip hsi hsp t).finish
        (finish_mem_vertices _)
      have hfirstP := alternatingPath_other_coordinate
        z i si r sr hir hsi hsr s
        (alternatingPath z i si r sr hir hsi hsr s).finish
        (finish_mem_vertices _) p (Ne.symm hip) (Ne.symm hrp)
      rw [hfirstP] at hmiddle
      exact hle.trans hmiddle

lemma shortDownwardInnerPath_vertices_on_two_spheres {d n : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ)
    (hz : z ∈ sphere d n) (hout : 0 ≤ si * z i)
    (hseparator : sr * z r = s)
    (hreservoir : ((2 * t : ℕ) : ℤ) ≤ sp * z p) :
    ∀ x ∈ (shortDownwardInnerPath z i r p si sr sp hir hip hrp
      hsi hsr hsp s t).vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
  let first := alternatingPath z i si r sr hir hsi hsr s
  have hsle : (s : ℤ) ≤ sr * z r := by omega
  have hfirstSphere : first.finish ∈ sphere d n :=
    finish_alternatingPath_mem_inner_sphere_of_signs
      z i si r sr hir hsi hsr s hz hout hsle
  have hfirstP : first.finish p = z p := by
    exact alternatingPath_other_coordinate z i si r sr hir hsi hsr s
      first.finish (finish_mem_vertices _) p (Ne.symm hip) (Ne.symm hrp)
  have hfirstR : sr * first.finish r = 0 := by
    rw [finish_alternatingPath]
    have hsrsq := sq_eq_one_of_natAbs_eq_one sr hsr
    simp only [Pi.add_apply, Pi.sub_apply, signedBasis_of_ne (Ne.symm hir),
      signedBasis_same]
    nlinarith
  have hfirstI : 0 ≤ si * first.finish i :=
    hout.trans (alternatingPath_private_coordinate_ge_start
      z i si r sr hir hsi hsr s first.finish (finish_mem_vertices _))
  have htFirst : (t : ℤ) ≤ sp * first.finish p := by
    rw [hfirstP]
    have hcast : ((2 * t : ℕ) : ℤ) = 2 * (t : ℤ) := by omega
    rw [hcast] at hreservoir
    omega
  have hmiddleSphere :
      (alternatingPath first.finish i si p sp hip hsi hsp t).finish ∈
        sphere d n :=
    finish_alternatingPath_mem_inner_sphere_of_signs
      first.finish i si p sp hip hsi hsp t hfirstSphere hfirstI htFirst
  have hmiddleR : sr *
      (alternatingPath first.finish i si p sp hip hsi hsp t).finish r = 0 := by
    have hcoord := alternatingPath_other_coordinate
      first.finish i si p sp hip hsi hsp t
      (alternatingPath first.finish i si p sp hip hsi hsp t).finish
      (finish_mem_vertices _) r (Ne.symm hir) hrp
    rw [hcoord, hfirstR]
  have htSecond : (t : ℤ) ≤ sp *
      (alternatingPath first.finish i si p sp hip hsi hsp t).finish p := by
    rw [finish_alternatingPath]
    have hspsq := sq_eq_one_of_natAbs_eq_one sp hsp
    simp only [Pi.add_apply, Pi.sub_apply, signedBasis_of_ne (Ne.symm hip),
      signedBasis_same]
    rw [hfirstP]
    have hcast : ((2 * t : ℕ) : ℤ) = 2 * (t : ℤ) := by omega
    rw [hcast] at hreservoir
    nlinarith
  intro x hx
  rcases mem_vertices_shortDownwardInnerPath z i r p si sr sp
      hir hip hrp hsi hsr hsp s t x hx with hx | hx
  · exact alternatingPath_vertices_on_two_spheres_of_signs
      z i si r sr hir hsi hsr s hz hout hsle x hx
  · apply continueAlternatingPath_vertices_on_two_spheres
      first.finish i si r (-sr) p sp hip hrp hsi
      (by simpa using hsr) hsp t t (Or.inl hir)
      hfirstSphere hfirstI htFirst hmiddleSphere
    · nlinarith [hmiddleR]
    · exact htSecond
    · simpa [first] using hx

private lemma continueAlternatingPath_eq_start_of_first_private_eq {d : ℕ}
    (z : LatticePoint d) (i r p : Fin d) (si sr sp : ℤ)
    (hir : i ≠ r) (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ) (hba : b ≤ a)
    (x : LatticePoint d)
    (hx : x ∈ (continueAlternatingPath z i si r sr p sp
      hip hrp hsi hsr hsp a b (Or.inl hir)).vertices)
    (heq : si * x i = si * z i) : x = z := by
  rcases mem_vertices_continueAlternatingPath z i si r sr p sp
      hip hrp hsi hsr hsp a b (Or.inl hir) x hx with hx | hx
  · exact alternatingPath_eq_start_of_private_coordinate_eq
      z i si p sp hip hsi hsp a x hx heq
  · have hcoord := alternatingPath_other_coordinate
      (alternatingPath z i si p sp hip hsi hsp a).finish
      r sr p sp hrp hsr hsp b x hx i hir hip
    have hfinish : si *
        (alternatingPath z i si p sp hip hsi hsp a).finish i =
        si * z i + a := by
      rw [finish_alternatingPath]
      have hsisq := sq_eq_one_of_natAbs_eq_one si hsi
      simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
        signedBasis_of_ne hip]
      nlinarith
    rw [← hcoord, heq] at hfinish
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a
    subst b
    have hfirst :
        (alternatingPath z i si p sp hip hsi hsp 0).finish = z := by
      rw [finish_alternatingPath]
      ext k
      simp [signedBasis]
    rw [hfirst] at hx
    rcases (mem_vertices_alternatingPath_iff
      z r sr p sp hrp hsr hsp 0 x).mp hx with ⟨k, hk, hkx⟩
    have hkzero : k = 0 := by omega
    subst k
    have hzero : alternatingVertex z r sr p sp 0 = z := by
      funext j
      simp [alternatingVertex, signedBasis]
    exact hkx.symm.trans hzero

lemma exceptionalDownward_common_vertices {d : ℕ}
    (z : LatticePoint d) (p r h : Fin d) (sp sr sh : ℤ)
    (hpr : p ≠ r) (hph : p ≠ h) (hrh : r ≠ h)
    (hsp : Int.natAbs sp = 1) (hsr : Int.natAbs sr = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s) :
    let first := alternatingPath z p sp r sr hpr hsp hsr s
    let second := continueAlternatingPath first.finish r (-sr) h sh p sp
      (Ne.symm hpr) (Ne.symm hph) (by simpa using hsr) hsh hsp
      (2 * t) t (Or.inl hrh)
    ∀ x, x ∈ first.vertices → x ∈ second.vertices → x = first.finish := by
  dsimp
  intro x hxFirst hxSecond
  have hfinishR : sr *
      (alternatingPath z p sp r sr hpr hsp hsr s).finish r = 0 := by
    rw [finish_alternatingPath]
    have hsrsq := sq_eq_one_of_natAbs_eq_one sr hsr
    simp only [Pi.add_apply, Pi.sub_apply,
      signedBasis_of_ne (Ne.symm hpr), signedBasis_same]
    nlinarith
  have hfirstLower : sr *
      (alternatingPath z p sp r sr hpr hsp hsr s).finish r ≤ sr * x r := by
    rcases (mem_vertices_alternatingPath_iff
      z p sp r sr hpr hsp hsr s x).mp hxFirst with ⟨k, hk, hkx⟩
    rw [← hkx,
      alternatingVertex_reservoir_coordinate z p sp r sr hpr hsr k,
      hseparator, hfinishR]
    omega
  have hsecondUpper : sr * x r ≤ sr *
      (alternatingPath z p sp r sr hpr hsp hsr s).finish r := by
    have hge := downwardContinuation_private_ge_start
      (alternatingPath z p sp r sr hpr hsp hsr s).finish
      r h p (-sr) (-sh) sp hrh (Ne.symm hpr) (Ne.symm hph)
      (by simpa using hsr) (by simpa using hsh) hsp (2 * t) t x (by
        simpa only [neg_neg] using hxSecond)
    nlinarith
  have heq : (-sr) * x r = (-sr) *
      (alternatingPath z p sp r sr hpr hsp hsr s).finish r := by
    have := le_antisymm hsecondUpper hfirstLower
    nlinarith
  exact continueAlternatingPath_eq_start_of_first_private_eq
    (alternatingPath z p sp r sr hpr hsp hsr s).finish
    r h p (-sr) sh sp hrh (Ne.symm hpr) (Ne.symm hph)
    (by simpa using hsr) hsh hsp (2 * t) t (by omega)
    x hxSecond heq

def exceptionalShortDownwardInnerPath {d : ℕ}
    (z : LatticePoint d) (p r h : Fin d) (sp sr sh : ℤ)
    (hpr : p ≠ r) (hph : p ≠ h) (hrh : r ≠ h)
    (hsp : Int.natAbs sp = 1) (hsr : Int.natAbs sr = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s) : LatticePath d :=
  let first := alternatingPath z p sp r sr hpr hsp hsr s
  let second := continueAlternatingPath first.finish r (-sr) h sh p sp
    (Ne.symm hpr) (Ne.symm hph) (by simpa using hsr) hsh hsp
    (2 * t) t (Or.inl hrh)
  join first second (by
    exact (start_continueAlternatingPath first.finish r (-sr) h sh p sp
      (Ne.symm hpr) (Ne.symm hph) (by simpa using hsr) hsh hsp
      (2 * t) t (Or.inl hrh)).symm)
    (exceptionalDownward_common_vertices z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator)

@[simp] lemma exceptionalShortDownwardInnerPath_start {d : ℕ}
    (z : LatticePoint d) (p r h : Fin d) (sp sr sh : ℤ)
    (hpr : p ≠ r) (hph : p ≠ h) (hrh : r ≠ h)
    (hsp : Int.natAbs sp = 1) (hsr : Int.natAbs sr = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s) :
    (exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator).start = z := by
  simp [exceptionalShortDownwardInnerPath]

@[simp] lemma exceptionalShortDownwardInnerPath_edgeLength {d : ℕ}
    (z : LatticePoint d) (p r h : Fin d) (sp sr sh : ℤ)
    (hpr : p ≠ r) (hph : p ≠ h) (hrh : r ≠ h)
    (hsp : Int.natAbs sp = 1) (hsr : Int.natAbs sr = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s) :
    (exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator).edgeLength = 2 * s + 6 * t := by
  simp [exceptionalShortDownwardInnerPath]
  omega

lemma mem_vertices_exceptionalShortDownwardInnerPath {d : ℕ}
    (z : LatticePoint d) (p r h : Fin d) (sp sr sh : ℤ)
    (hpr : p ≠ r) (hph : p ≠ h) (hrh : r ≠ h)
    (hsp : Int.natAbs sp = 1) (hsr : Int.natAbs sr = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s) (x : LatticePoint d)
    (hx : x ∈ (exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator).vertices) :
    x ∈ (alternatingPath z p sp r sr hpr hsp hsr s).vertices ∨
      x ∈ (continueAlternatingPath
        (alternatingPath z p sp r sr hpr hsp hsr s).finish
        r (-sr) h sh p sp (Ne.symm hpr) (Ne.symm hph)
        (by simpa using hsr) hsh hsp (2 * t) t (Or.inl hrh)).vertices := by
  change x ∈ (alternatingPath z p sp r sr hpr hsp hsr s).vertices ++
    (continueAlternatingPath
      (alternatingPath z p sp r sr hpr hsp hsr s).finish
      r (-sr) h sh p sp (Ne.symm hpr) (Ne.symm hph)
      (by simpa using hsr) hsh hsp (2 * t) t
      (Or.inl hrh)).vertices.tail at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (List.mem_of_mem_tail hx)

lemma exceptionalShortDownwardInnerPath_finish_separator_coordinate {d : ℕ}
    (z : LatticePoint d) (p r h : Fin d) (sp sr sh : ℤ)
    (hpr : p ≠ r) (hph : p ≠ h) (hrh : r ≠ h)
    (hsp : Int.natAbs sp = 1) (hsr : Int.natAbs sr = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s) :
    sr * (exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator).finish r =
      sr * z r - s - 2 * t := by
  simp only [exceptionalShortDownwardInnerPath, finish_join,
    finish_continueAlternatingPath, finish_alternatingPath, Pi.add_apply,
    Pi.sub_apply, signedBasis_same,
    signedBasis_of_ne (Ne.symm hpr), signedBasis_of_ne hrh]
  have hsrsq := sq_eq_one_of_natAbs_eq_one sr hsr
  push_cast
  nlinarith

lemma exceptionalShortDownwardInnerPath_finish_helper_coordinate {d : ℕ}
    (z : LatticePoint d) (p r h : Fin d) (sp sr sh : ℤ)
    (hpr : p ≠ r) (hph : p ≠ h) (hrh : r ≠ h)
    (hsp : Int.natAbs sp = 1) (hsr : Int.natAbs sr = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s) :
    sh * (exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator).finish h = sh * z h + t := by
  simp only [exceptionalShortDownwardInnerPath, finish_join,
    finish_continueAlternatingPath, finish_alternatingPath, Pi.add_apply,
    Pi.sub_apply, signedBasis_same, signedBasis_of_ne (Ne.symm hph),
    signedBasis_of_ne (Ne.symm hrh)]
  have hshsq := sq_eq_one_of_natAbs_eq_one sh hsh
  nlinarith

lemma exceptionalShortDownwardInnerPath_finish_reservoir_coordinate {d : ℕ}
    (z : LatticePoint d) (p r h : Fin d) (sp sr sh : ℤ)
    (hpr : p ≠ r) (hph : p ≠ h) (hrh : r ≠ h)
    (hsp : Int.natAbs sp = 1) (hsr : Int.natAbs sr = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s) :
    sp * (exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator).finish p =
      sp * z p + s - 3 * t := by
  simp only [exceptionalShortDownwardInnerPath, finish_join,
    finish_continueAlternatingPath, finish_alternatingPath, Pi.add_apply,
    Pi.sub_apply, signedBasis_same, signedBasis_of_ne hpr,
    signedBasis_of_ne hph]
  have hspsq := sq_eq_one_of_natAbs_eq_one sp hsp
  push_cast
  nlinarith

lemma exceptionalShortDownwardInnerPath_separator_coordinate_le_start {d : ℕ}
    (z : LatticePoint d) (p r h : Fin d) (sp sr sh : ℤ)
    (hpr : p ≠ r) (hph : p ≠ h) (hrh : r ≠ h)
    (hsp : Int.natAbs sp = 1) (hsr : Int.natAbs sr = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s) (x : LatticePoint d)
    (hx : x ∈ (exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator).vertices) :
    sr * x r ≤ sr * z r := by
  rcases mem_vertices_exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator x hx with hx | hx
  · exact alternatingPath_reservoir_coordinate_le_start
      z p sp r sr hpr hsp hsr s x hx
  · have hfirst := alternatingPath_reservoir_coordinate_le_start
      z p sp r sr hpr hsp hsr s
      (alternatingPath z p sp r sr hpr hsp hsr s).finish
      (finish_mem_vertices _)
    have hge := downwardContinuation_private_ge_start
        (alternatingPath z p sp r sr hpr hsp hsr s).finish
        r h p (-sr) (-sh) sp hrh (Ne.symm hpr) (Ne.symm hph)
        (by simpa using hsr) (by simpa using hsh) hsp
        (2 * t) t x (by simpa only [neg_neg] using hx)
    have hsecond : sr * x r ≤ sr *
        (alternatingPath z p sp r sr hpr hsp hsr s).finish r := by
      nlinarith
    exact hsecond.trans hfirst

lemma exceptionalShortDownwardInnerPath_helper_coordinate_ge_start {d : ℕ}
    (z : LatticePoint d) (p r h : Fin d) (sp sr sh : ℤ)
    (hpr : p ≠ r) (hph : p ≠ h) (hrh : r ≠ h)
    (hsp : Int.natAbs sp = 1) (hsr : Int.natAbs sr = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s) (x : LatticePoint d)
    (hx : x ∈ (exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator).vertices) :
    sh * z h ≤ sh * x h := by
  rcases mem_vertices_exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator x hx with hx | hx
  · have hxcoord := alternatingPath_other_coordinate
      z p sp r sr hpr hsp hsr s x hx h (Ne.symm hph) (Ne.symm hrh)
    rw [hxcoord]
  · rcases mem_vertices_continueAlternatingPath
      (alternatingPath z p sp r sr hpr hsp hsr s).finish
      r (-sr) h sh p sp (Ne.symm hpr) (Ne.symm hph)
      (by simpa using hsr) hsh hsp (2 * t) t (Or.inl hrh)
      x hx with hx | hx
    · have hxcoord := alternatingPath_other_coordinate
        (alternatingPath z p sp r sr hpr hsp hsr s).finish
        r (-sr) p sp (Ne.symm hpr) (by simpa using hsr) hsp
        (2 * t) x hx h (Ne.symm hrh) (Ne.symm hph)
      have hfirstH := alternatingPath_other_coordinate
        z p sp r sr hpr hsp hsr s
        (alternatingPath z p sp r sr hpr hsp hsr s).finish
        (finish_mem_vertices _) h (Ne.symm hph) (Ne.symm hrh)
      rw [hxcoord, hfirstH]
    · have hge := alternatingPath_private_coordinate_ge_start
        (alternatingPath
          (alternatingPath z p sp r sr hpr hsp hsr s).finish
          r (-sr) p sp (Ne.symm hpr) (by simpa using hsr) hsp
          (2 * t)).finish
        h sh p sp (Ne.symm hph) hsh hsp t x hx
      have hmiddleH := alternatingPath_other_coordinate
        (alternatingPath z p sp r sr hpr hsp hsr s).finish
        r (-sr) p sp (Ne.symm hpr) (by simpa using hsr) hsp (2 * t)
        (alternatingPath
          (alternatingPath z p sp r sr hpr hsp hsr s).finish
          r (-sr) p sp (Ne.symm hpr) (by simpa using hsr) hsp
          (2 * t)).finish
        (finish_mem_vertices _) h (Ne.symm hrh) (Ne.symm hph)
      have hfirstH := alternatingPath_other_coordinate
        z p sp r sr hpr hsp hsr s
        (alternatingPath z p sp r sr hpr hsp hsr s).finish
        (finish_mem_vertices _) h (Ne.symm hph) (Ne.symm hrh)
      rw [hmiddleH, hfirstH] at hge
      exact hge

lemma exceptionalShortDownwardInnerPath_helper_coordinate_le_finish {d : ℕ}
    (z : LatticePoint d) (p r h : Fin d) (sp sr sh : ℤ)
    (hpr : p ≠ r) (hph : p ≠ h) (hrh : r ≠ h)
    (hsp : Int.natAbs sp = 1) (hsr : Int.natAbs sr = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s) (x : LatticePoint d)
    (hx : x ∈ (exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator).vertices) :
    sh * x h ≤ sh *
      (exceptionalShortDownwardInnerPath z p r h sp sr sh
        hpr hph hrh hsp hsr hsh s t hseparator).finish h := by
  have hfinish := exceptionalShortDownwardInnerPath_finish_helper_coordinate
    z p r h sp sr sh hpr hph hrh hsp hsr hsh s t hseparator
  rcases mem_vertices_exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator x hx with hx | hx
  · have hxcoord := alternatingPath_other_coordinate
      z p sp r sr hpr hsp hsr s x hx h (Ne.symm hph) (Ne.symm hrh)
    rw [hfinish, hxcoord]
    omega
  · rcases mem_vertices_continueAlternatingPath
      (alternatingPath z p sp r sr hpr hsp hsr s).finish
      r (-sr) h sh p sp (Ne.symm hpr) (Ne.symm hph)
      (by simpa using hsr) hsh hsp (2 * t) t (Or.inl hrh)
      x hx with hx | hx
    · have hxcoord := alternatingPath_other_coordinate
        (alternatingPath z p sp r sr hpr hsp hsr s).finish
        r (-sr) p sp (Ne.symm hpr) (by simpa using hsr) hsp
        (2 * t) x hx h (Ne.symm hrh) (Ne.symm hph)
      have hfirstH := alternatingPath_other_coordinate
        z p sp r sr hpr hsp hsr s
        (alternatingPath z p sp r sr hpr hsp hsr s).finish
        (finish_mem_vertices _) h (Ne.symm hph) (Ne.symm hrh)
      rw [hfinish, hxcoord, hfirstH]
      omega
    · have hle := alternatingPath_private_coordinate_le_finish
        (alternatingPath
          (alternatingPath z p sp r sr hpr hsp hsr s).finish
          r (-sr) p sp (Ne.symm hpr) (by simpa using hsr) hsp
          (2 * t)).finish
        h sh p sp (Ne.symm hph) hsh hsp t x hx
      have hfinal : sh *
          (alternatingPath
            (alternatingPath
              (alternatingPath z p sp r sr hpr hsp hsr s).finish
              r (-sr) p sp (Ne.symm hpr) (by simpa using hsr) hsp
              (2 * t)).finish
            h sh p sp (Ne.symm hph) hsh hsp t).finish h =
          sh * z h + t := by
        simp only [finish_alternatingPath, Pi.add_apply, Pi.sub_apply,
          signedBasis_same, signedBasis_of_ne (Ne.symm hph),
          signedBasis_of_ne (Ne.symm hrh)]
        have hshsq := sq_eq_one_of_natAbs_eq_one sh hsh
        nlinarith
      rw [hfinal] at hle
      rw [hfinish]
      exact hle

lemma exceptionalShortDownwardInnerPath_other_coordinate {d : ℕ}
    (z : LatticePoint d) (p r h : Fin d) (sp sr sh : ℤ)
    (hpr : p ≠ r) (hph : p ≠ h) (hrh : r ≠ h)
    (hsp : Int.natAbs sp = 1) (hsr : Int.natAbs sr = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s) (x : LatticePoint d)
    (hx : x ∈ (exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator).vertices)
    (k : Fin d) (hkp : k ≠ p) (hkr : k ≠ r) (hkh : k ≠ h) :
    x k = z k := by
  rcases mem_vertices_exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator x hx with hx | hx
  · exact alternatingPath_other_coordinate
      z p sp r sr hpr hsp hsr s x hx k hkp hkr
  · rcases mem_vertices_continueAlternatingPath
      (alternatingPath z p sp r sr hpr hsp hsr s).finish
      r (-sr) h sh p sp (Ne.symm hpr) (Ne.symm hph)
      (by simpa using hsr) hsh hsp (2 * t) t (Or.inl hrh)
      x hx with hx | hx
    · rw [alternatingPath_other_coordinate
          (alternatingPath z p sp r sr hpr hsp hsr s).finish
          r (-sr) p sp (Ne.symm hpr) (by simpa using hsr) hsp
          (2 * t) x hx k hkr hkp,
        alternatingPath_other_coordinate z p sp r sr hpr hsp hsr s
          (alternatingPath z p sp r sr hpr hsp hsr s).finish
          (finish_mem_vertices _) k hkp hkr]
    · rw [alternatingPath_other_coordinate
          (alternatingPath
            (alternatingPath z p sp r sr hpr hsp hsr s).finish
            r (-sr) p sp (Ne.symm hpr) (by simpa using hsr) hsp
            (2 * t)).finish
          h sh p sp (Ne.symm hph) hsh hsp t x hx k hkh hkp,
        alternatingPath_other_coordinate
          (alternatingPath z p sp r sr hpr hsp hsr s).finish
          r (-sr) p sp (Ne.symm hpr) (by simpa using hsr) hsp (2 * t)
          (alternatingPath
            (alternatingPath z p sp r sr hpr hsp hsr s).finish
            r (-sr) p sp (Ne.symm hpr) (by simpa using hsr) hsp
            (2 * t)).finish
          (finish_mem_vertices _) k hkr hkp,
        alternatingPath_other_coordinate z p sp r sr hpr hsp hsr s
          (alternatingPath z p sp r sr hpr hsp hsr s).finish
          (finish_mem_vertices _) k hkp hkr]

lemma exceptionalShortDownwardInnerPath_vertices_on_two_spheres {d n : ℕ}
    (z : LatticePoint d) (p r h : Fin d) (sp sr sh : ℤ)
    (hpr : p ≠ r) (hph : p ≠ h) (hrh : r ≠ h)
    (hsp : Int.natAbs sp = 1) (hsr : Int.natAbs sr = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hz : z ∈ sphere d n) (houtP : 0 ≤ sp * z p)
    (houtH : 0 ≤ sh * z h) (hseparator : sr * z r = s)
    (hreservoir : ((3 * t : ℕ) : ℤ) ≤ sp * z p + s) :
    ∀ x ∈ (exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator).vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
  let first := alternatingPath z p sp r sr hpr hsp hsr s
  have hsle : (s : ℤ) ≤ sr * z r := by omega
  have hfirstSphere : first.finish ∈ sphere d n :=
    finish_alternatingPath_mem_inner_sphere_of_signs
      z p sp r sr hpr hsp hsr s hz houtP hsle
  have hfirstP : sp * first.finish p = sp * z p + s := by
    rw [finish_alternatingPath]
    have hspsq := sq_eq_one_of_natAbs_eq_one sp hsp
    simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
      signedBasis_of_ne hpr]
    nlinarith
  have hfirstH : first.finish h = z h := by
    exact alternatingPath_other_coordinate z p sp r sr hpr hsp hsr s
      first.finish (finish_mem_vertices _) h (Ne.symm hph) (Ne.symm hrh)
  have hfirstR : sr * first.finish r = 0 := by
    rw [finish_alternatingPath]
    have hsrsq := sq_eq_one_of_natAbs_eq_one sr hsr
    simp only [Pi.add_apply, Pi.sub_apply, signedBasis_of_ne (Ne.symm hpr),
      signedBasis_same]
    nlinarith
  have houtHFirst : 0 ≤ sh * first.finish h := by
    rw [hfirstH]
    exact houtH
  have htwoFirst : ((2 * t : ℕ) : ℤ) ≤ sp * first.finish p := by
    rw [hfirstP]
    have hcast : ((3 * t : ℕ) : ℤ) = 3 * (t : ℤ) := by omega
    rw [hcast] at hreservoir
    omega
  have hmiddleSphere :
      (alternatingPath first.finish r (-sr) p sp (Ne.symm hpr)
        (by simpa using hsr) hsp (2 * t)).finish ∈ sphere d n :=
    finish_alternatingPath_mem_inner_sphere_of_signs
      first.finish r (-sr) p sp (Ne.symm hpr)
      (by simpa using hsr) hsp (2 * t) hfirstSphere
      (by nlinarith [hfirstR]) htwoFirst
  have hmiddleH :
      (alternatingPath first.finish r (-sr) p sp (Ne.symm hpr)
        (by simpa using hsr) hsp (2 * t)).finish h = first.finish h := by
    have hcoord := alternatingPath_other_coordinate
      first.finish r (-sr) p sp (Ne.symm hpr) (by simpa using hsr) hsp
      (2 * t)
      (alternatingPath first.finish r (-sr) p sp (Ne.symm hpr)
        (by simpa using hsr) hsp (2 * t)).finish
      (finish_mem_vertices _) h (Ne.symm hrh) (Ne.symm hph)
    exact hcoord
  have houtHMiddle : 0 ≤ sh *
      (alternatingPath first.finish r (-sr) p sp (Ne.symm hpr)
        (by simpa using hsr) hsp (2 * t)).finish h := by
    rw [hmiddleH]
    exact houtHFirst
  have htSecond : (t : ℤ) ≤ sp *
      (alternatingPath first.finish r (-sr) p sp (Ne.symm hpr)
        (by simpa using hsr) hsp (2 * t)).finish p := by
    rw [finish_alternatingPath]
    have hspsq := sq_eq_one_of_natAbs_eq_one sp hsp
    simp only [Pi.add_apply, Pi.sub_apply,
      signedBasis_of_ne hpr, signedBasis_same]
    push_cast at hreservoir ⊢
    nlinarith [hfirstP]
  intro x hx
  rcases mem_vertices_exceptionalShortDownwardInnerPath z p r h sp sr sh
      hpr hph hrh hsp hsr hsh s t hseparator x hx with hx | hx
  · exact alternatingPath_vertices_on_two_spheres_of_signs
      z p sp r sr hpr hsp hsr s hz houtP hsle x hx
  · apply continueAlternatingPath_vertices_on_two_spheres
      first.finish r (-sr) h sh p sp (Ne.symm hpr) (Ne.symm hph)
      (by simpa using hsr) hsh hsp (2 * t) t (Or.inl hrh)
      hfirstSphere (by nlinarith [hfirstR]) htwoFirst hmiddleSphere
    · exact houtHMiddle
    · exact htSecond
    · simpa [first] using hx

private lemma innerFanIndex_direction_ne' {d : ℕ} {z : LatticePoint d}
    {r : Fin d} {q v : InnerFanIndex z r} (hqv : q ≠ v) :
    q.1.1 ≠ v.1.1 ∨ boolSign q.1.2 ≠ boolSign v.1.2 := by
  by_contra h
  have h := not_or.mp h
  apply hqv
  apply Subtype.ext
  apply Prod.ext (not_ne_iff.mp h.1)
  exact boolSign_injective (not_ne_iff.mp h.2)

private lemma boolSign_eq_neg_of_ne {a b : Bool}
    (h : boolSign a ≠ boolSign b) : boolSign b = -boolSign a := by
  cases a <;> cases b <;> simp_all [boolSign]

lemma shortDownwardInnerPaths_edgeDisjoint {d : ℕ}
    (z : LatticePoint d) (r p : Fin d) (sr sp : ℤ)
    (hrp : r ≠ p) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ) (hs : 0 < s)
    {q v : InnerFanIndex z r} (hqp : q.1.1 ≠ p) (hvp : v.1.1 ≠ p)
    (hqv : q ≠ v) :
    Disjoint
      (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
        q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t).edgeSet
      (shortDownwardInnerPath z v.1.1 r p (boolSign v.1.2) sr sp
        v.2.2 hvp hrp (natAbs_boolSign _) hsr hsp s t).edgeSet := by
  apply edgeDisjoint_of_common_vertices_subsingleton _ _ z
  intro x hxq hxv
  apply shortDownwardInnerPath_eq_start_of_private_coordinate_eq
    z q.1.1 r p (boolSign q.1.2) sr sp q.2.2 hqp hrp
    (natAbs_boolSign _) hsr hsp s t hs x hxq
  by_cases hcoord : q.1.1 ≠ v.1.1
  · have hxcoord := shortDownwardInnerPath_other_coordinate
      z v.1.1 r p (boolSign v.1.2) sr sp v.2.2 hvp hrp
      (natAbs_boolSign _) hsr hsp s t x hxv q.1.1
      hcoord q.2.2 hqp
    rw [hxcoord]
  · have hsame : q.1.1 = v.1.1 := not_ne_iff.mp hcoord
    have hsign := (innerFanIndex_direction_ne' hqv).resolve_left hcoord
    have hopposite : boolSign v.1.2 = -boolSign q.1.2 :=
      boolSign_eq_neg_of_ne hsign
    have hqge := shortDownwardInnerPath_private_coordinate_ge_start
      z q.1.1 r p (boolSign q.1.2) sr sp q.2.2 hqp hrp
      (natAbs_boolSign _) hsr hsp s t x hxq
    have hvgeRaw := shortDownwardInnerPath_private_coordinate_ge_start
      z v.1.1 r p (boolSign v.1.2) sr sp v.2.2 hvp hrp
      (natAbs_boolSign _) hsr hsp s t x hxv
    have hvge : boolSign v.1.2 * z q.1.1 ≤
        boolSign v.1.2 * x q.1.1 := by simpa [hsame] using hvgeRaw
    have hqout := q.2.1
    have hvout : 0 ≤ boolSign v.1.2 * z q.1.1 := by
      simpa [IsOutwardDirection, hsame] using v.2.1
    rw [hopposite] at hvge hvout
    have hsq := sq_eq_one_of_natAbs_eq_one
      (boolSign q.1.2) (natAbs_boolSign q.1.2)
    nlinarith

lemma shortDownwardInnerPath_endpoint_far_of_distinct {d : ℕ}
    (z : LatticePoint d) (r p : Fin d) (sr sp : ℤ)
    (hrp : r ≠ p) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (s t : ℕ)
    (rsep : ℝ) (hrsep : rsep ≤ (s + t : ℕ))
    {q v : InnerFanIndex z r} (hqp : q.1.1 ≠ p) (hvp : v.1.1 ≠ p)
    (hqv : q ≠ v) :
    ∀ x ∈ (shortDownwardInnerPath z v.1.1 r p (boolSign v.1.2) sr sp
      v.2.2 hvp hrp (natAbs_boolSign _) hsr hsp s t).vertices,
      rsep ≤ (l1Dist
        (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
          q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t).finish x : ℝ) := by
  apply endpoint_far_from_vertices_of_signed_coordinate_gap
    (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
      q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t)
    (shortDownwardInnerPath z v.1.1 r p (boolSign v.1.2) sr sp
      v.2.2 hvp hrp (natAbs_boolSign _) hsr hsp s t)
    q.1.1 (boolSign q.1.2) (natAbs_boolSign q.1.2)
    rsep (boolSign q.1.2 * z q.1.1) (s + t) hrsep
    (by positivity)
  · rw [shortDownwardInnerPath_finish_private_coordinate]
    push_cast
    omega
  · intro x hx
    by_cases hcoord : q.1.1 ≠ v.1.1
    · have hxcoord := shortDownwardInnerPath_other_coordinate
        z v.1.1 r p (boolSign v.1.2) sr sp v.2.2 hvp hrp
        (natAbs_boolSign _) hsr hsp s t x hx q.1.1
        hcoord q.2.2 hqp
      rw [hxcoord]
    · have hsame : q.1.1 = v.1.1 := not_ne_iff.mp hcoord
      have hsign := (innerFanIndex_direction_ne' hqv).resolve_left hcoord
      have hopposite : boolSign v.1.2 = -boolSign q.1.2 :=
        boolSign_eq_neg_of_ne hsign
      have hvgeRaw := shortDownwardInnerPath_private_coordinate_ge_start
        z v.1.1 r p (boolSign v.1.2) sr sp v.2.2 hvp hrp
        (natAbs_boolSign _) hsr hsp s t x hx
      have hvge : boolSign v.1.2 * z q.1.1 ≤
          boolSign v.1.2 * x q.1.1 := by simpa [hsame] using hvgeRaw
      rw [hopposite] at hvge
      nlinarith

lemma shortDownwardInnerPath_edgeDisjoint_exceptional {d : ℕ}
    (z : LatticePoint d) (r p h : Fin d) (sr sp sh : ℤ)
    (hrp : r ≠ p) (hph : p ≠ h) (hrh : r ≠ h)
    (hsr : Int.natAbs sr = 1) (hsp : Int.natAbs sp = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (hseparator : sr * z r = s)
    (q : InnerFanIndex z r) (hqp : q.1.1 ≠ p) :
    Disjoint
      (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
        q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t).edgeSet
      (exceptionalShortDownwardInnerPath z p r h sp sr sh
        (Ne.symm hrp) hph hrh hsp hsr hsh s t hseparator).edgeSet := by
  apply edgeDisjoint_of_common_vertices_subsingleton _ _ z
  intro x hxq hxe
  apply shortDownwardInnerPath_eq_start_of_private_coordinate_eq
    z q.1.1 r p (boolSign q.1.2) sr sp q.2.2 hqp hrp
    (natAbs_boolSign _) hsr hsp s t hs x hxq
  by_cases hqh : q.1.1 ≠ h
  · have hxcoord := exceptionalShortDownwardInnerPath_other_coordinate
      z p r h sp sr sh (Ne.symm hrp) hph hrh hsp hsr hsh
      s t hseparator x hxe q.1.1 hqp q.2.2 hqh
    rw [hxcoord]
  · have hqh' : q.1.1 = h := not_ne_iff.mp hqh
    rcases mem_vertices_exceptionalShortDownwardInnerPath
        z p r h sp sr sh (Ne.symm hrp) hph hrh hsp hsr hsh
        s t hseparator x hxe with hx | hx
    · have hxcoord := alternatingPath_other_coordinate
        z p sp r sr (Ne.symm hrp) hsp hsr s x hx q.1.1
        hqp q.2.2
      rw [hxcoord]
    · rcases mem_vertices_continueAlternatingPath
        (alternatingPath z p sp r sr (Ne.symm hrp) hsp hsr s).finish
        r (-sr) h sh p sp hrp (Ne.symm hph) (by simpa using hsr)
        hsh hsp (2 * t) t (Or.inl hrh) x hx with hx | hx
      · have hxcoord := alternatingPath_other_coordinate
          (alternatingPath z p sp r sr (Ne.symm hrp) hsp hsr s).finish
          r (-sr) p sp hrp (by simpa using hsr) hsp (2 * t)
          x hx q.1.1 (by simpa [hqh'] using Ne.symm hrh) hqp
        have hfirstCoord := alternatingPath_other_coordinate
          z p sp r sr (Ne.symm hrp) hsp hsr s
          (alternatingPath z p sp r sr (Ne.symm hrp) hsp hsr s).finish
          (finish_mem_vertices _) q.1.1 hqp q.2.2
        rw [hxcoord, hfirstCoord]
      · exfalso
        have hordinary := shortDownwardInnerPath_finish_separator_le_coordinate
          z q.1.1 r p (boolSign q.1.2) sr sp q.2.2 hqp hrp
          (natAbs_boolSign _) hsr hsp s t hseparator x hxq
        have hordinaryFinish := shortDownwardInnerPath_finish_separator_coordinate
          z q.1.1 r p (boolSign q.1.2) sr sp q.2.2 hqp hrp
          (natAbs_boolSign _) hsr hsp s t
        have hxR := alternatingPath_other_coordinate
          (alternatingPath
            (alternatingPath z p sp r sr (Ne.symm hrp) hsp hsr s).finish
            r (-sr) p sp hrp (by simpa using hsr) hsp (2 * t)).finish
          h sh p sp (Ne.symm hph) hsh hsp t x hx r
          hrh hrp
        have hmiddleR : sr *
            (alternatingPath
              (alternatingPath z p sp r sr (Ne.symm hrp) hsp hsr s).finish
              r (-sr) p sp hrp (by simpa using hsr) hsp (2 * t)).finish r =
            sr * z r - s - 2 * t := by
          simp only [finish_alternatingPath, Pi.add_apply, Pi.sub_apply,
            signedBasis_same, signedBasis_of_ne hrp]
          have hsrsq := sq_eq_one_of_natAbs_eq_one sr hsr
          push_cast
          nlinarith
        rw [hordinaryFinish, hseparator] at hordinary
        rw [hxR, hmiddleR, hseparator] at hordinary
        omega

lemma exceptionalShortDownwardInnerPath_endpoint_far_ordinary {d : ℕ}
    (z : LatticePoint d) (r p h : Fin d) (sr sp sh : ℤ)
    (hrp : r ≠ p) (hph : p ≠ h) (hrh : r ≠ h)
    (hsr : Int.natAbs sr = 1) (hsp : Int.natAbs sp = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s)
    (q : InnerFanIndex z r) (hqp : q.1.1 ≠ p)
    (rsep : ℝ) (hrsep : rsep ≤ (((s + t) / 6 : ℕ) : ℝ)) :
    ∀ x ∈ (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
      q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t).vertices,
      rsep ≤ (l1Dist
        (exceptionalShortDownwardInnerPath z p r h sp sr sh
          (Ne.symm hrp) hph hrh hsp hsr hsh s t hseparator).finish x : ℝ) := by
  let k : ℕ := (s + t) / 6
  by_cases hkt : k ≤ t
  ·
    by_cases hqh : q.1.1 = h
    · apply endpoint_far_from_vertices_of_signed_coordinate_gap
        (exceptionalShortDownwardInnerPath z p r h sp sr sh
          (Ne.symm hrp) hph hrh hsp hsr hsh s t hseparator)
        (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
          q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t)
        r (-sr) (by simpa using hsr) rsep
        (-sr * z r + s + t) (k : ℤ)
        (by simpa only [Int.cast_natCast] using hrsep) (by positivity)
      · have hef := exceptionalShortDownwardInnerPath_finish_separator_coordinate
          z p r h sp sr sh (Ne.symm hrp) hph hrh hsp hsr hsh
          s t hseparator
        push_cast at hef ⊢
        have hsrsq := sq_eq_one_of_natAbs_eq_one sr hsr
        nlinarith [hef]
      · intro x hx
        have hlower := shortDownwardInnerPath_finish_separator_le_coordinate
          z q.1.1 r p (boolSign q.1.2) sr sp q.2.2 hqp hrp
          (natAbs_boolSign _) hsr hsp s t hseparator x hx
        have hfinish := shortDownwardInnerPath_finish_separator_coordinate
          z q.1.1 r p (boolSign q.1.2) sr sp q.2.2 hqp hrp
          (natAbs_boolSign _) hsr hsp s t
        rw [hfinish] at hlower
        nlinarith
    · apply endpoint_far_from_vertices_of_signed_coordinate_gap
        (exceptionalShortDownwardInnerPath z p r h sp sr sh
          (Ne.symm hrp) hph hrh hsp hsr hsh s t hseparator)
        (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
          q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t)
        h sh hsh rsep (sh * z h) (k : ℤ)
        (by simpa only [Int.cast_natCast] using hrsep) (by positivity)
      · rw [exceptionalShortDownwardInnerPath_finish_helper_coordinate]
        push_cast
        omega
      · intro x hx
        have hxcoord := shortDownwardInnerPath_other_coordinate
          z q.1.1 r p (boolSign q.1.2) sr sp q.2.2 hqp hrp
          (natAbs_boolSign _) hsr hsp s t x hx h (Ne.symm hqh)
          (Ne.symm hrh) (Ne.symm hph)
        rw [hxcoord]
  ·
    have hk : k ≤ s - 3 * t := by
      dsimp [k]
      omega
    apply endpoint_far_from_vertices_of_signed_coordinate_gap
      (exceptionalShortDownwardInnerPath z p r h sp sr sh
        (Ne.symm hrp) hph hrh hsp hsr hsh s t hseparator)
      (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
        q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t)
      p sp hsp rsep (sp * z p) (k : ℤ)
      (by simpa only [Int.cast_natCast] using hrsep) (by positivity)
    · rw [exceptionalShortDownwardInnerPath_finish_reservoir_coordinate]
      push_cast
      omega
    · intro x hx
      exact shortDownwardInnerPath_reservoir_coordinate_le_start
        z q.1.1 r p (boolSign q.1.2) sr sp q.2.2 hqp hrp
        (natAbs_boolSign _) hsr hsp s t x hx

lemma shortDownwardInnerPath_endpoint_far_exceptional {d : ℕ}
    (z : LatticePoint d) (r p h : Fin d) (sr sp sh : ℤ)
    (hrp : r ≠ p) (hph : p ≠ h) (hrh : r ≠ h)
    (hsr : Int.natAbs sr = 1) (hsp : Int.natAbs sp = 1)
    (hsh : Int.natAbs sh = 1) (s t : ℕ)
    (hseparator : sr * z r = s)
    (q : InnerFanIndex z r) (hqp : q.1.1 ≠ p)
    (rsep : ℝ) (hrsep : rsep ≤ (((s + t) / 6 : ℕ) : ℝ)) :
    ∀ x ∈ (exceptionalShortDownwardInnerPath z p r h sp sr sh
      (Ne.symm hrp) hph hrh hsp hsr hsh s t hseparator).vertices,
      rsep ≤ (l1Dist
        (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
          q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t).finish x : ℝ) := by
  let k : ℕ := (s + t) / 6
  by_cases hqh : q.1.1 = h
  · by_cases hsign : boolSign q.1.2 = sh
    · have hordinaryHelper : sh *
          (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
            q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t).finish h =
          sh * z h + s + t := by
        have hof := shortDownwardInnerPath_finish_private_coordinate
          z q.1.1 r p (boolSign q.1.2) sr sp q.2.2 hqp hrp
          (natAbs_boolSign _) hsr hsp s t
        rw [← hsign, ← hqh]
        exact hof
      by_cases hkt : k ≤ t
      · intro x hx
        rcases mem_vertices_exceptionalShortDownwardInnerPath
            z p r h sp sr sh (Ne.symm hrp) hph hrh hsp hsr hsh
            s t hseparator x hx with hx | hx
        · apply endpoint_far_from_vertices_of_signed_coordinate_gap
            (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
              q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t)
            (alternatingPath z p sp r sr (Ne.symm hrp) hsp hsr s)
            h sh hsh rsep (sh * z h) (k : ℤ)
            (by simpa only [Int.cast_natCast] using hrsep) (by positivity)
          · rw [hordinaryHelper]
            push_cast
            omega
          · intro y hy
            have hycoord := alternatingPath_other_coordinate
              z p sp r sr (Ne.symm hrp) hsp hsr s y hy h
              (Ne.symm hph) (Ne.symm hrh)
            rw [hycoord]
          · exact hx
        · rcases mem_vertices_continueAlternatingPath
            (alternatingPath z p sp r sr (Ne.symm hrp) hsp hsr s).finish
            r (-sr) h sh p sp hrp (Ne.symm hph) (by simpa using hsr)
            hsh hsp (2 * t) t (Or.inl hrh) x hx with hx | hx
          · apply endpoint_far_from_vertices_of_signed_coordinate_gap
              (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
                q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t)
              (alternatingPath
                (alternatingPath z p sp r sr (Ne.symm hrp) hsp hsr s).finish
                r (-sr) p sp hrp (by simpa using hsr) hsp (2 * t))
              h sh hsh rsep (sh * z h) (k : ℤ)
              (by simpa only [Int.cast_natCast] using hrsep) (by positivity)
            · rw [hordinaryHelper]
              push_cast
              omega
            · intro y hy
              have hycoord := alternatingPath_other_coordinate
                (alternatingPath z p sp r sr (Ne.symm hrp) hsp hsr s).finish
                r (-sr) p sp hrp (by simpa using hsr) hsp (2 * t)
                y hy h (Ne.symm hrh) (Ne.symm hph)
              have hfirstH := alternatingPath_other_coordinate
                z p sp r sr (Ne.symm hrp) hsp hsr s
                (alternatingPath z p sp r sr (Ne.symm hrp) hsp hsr s).finish
                (finish_mem_vertices _) h (Ne.symm hph) (Ne.symm hrh)
              rw [hycoord, hfirstH]
            · exact hx
          · apply endpoint_far_from_vertices_of_signed_coordinate_gap
              (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
                q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t)
              (alternatingPath
                (alternatingPath
                  (alternatingPath z p sp r sr (Ne.symm hrp) hsp hsr s).finish
                  r (-sr) p sp hrp (by simpa using hsr) hsp (2 * t)).finish
                h sh p sp (Ne.symm hph) hsh hsp t)
              r sr hsr rsep (sr * z r - s - 2 * t) (k : ℤ)
              (by simpa only [Int.cast_natCast] using hrsep) (by positivity)
            · rw [shortDownwardInnerPath_finish_separator_coordinate]
              push_cast
              omega
            · intro y hy
              have hycoord := alternatingPath_other_coordinate
                (alternatingPath
                  (alternatingPath z p sp r sr (Ne.symm hrp) hsp hsr s).finish
                  r (-sr) p sp hrp (by simpa using hsr) hsp (2 * t)).finish
                h sh p sp (Ne.symm hph) hsh hsp t y hy r hrh hrp
              have hmiddleR : sr *
                  (alternatingPath
                    (alternatingPath z p sp r sr (Ne.symm hrp) hsp hsr s).finish
                    r (-sr) p sp hrp (by simpa using hsr) hsp (2 * t)).finish r =
                  sr * z r - s - 2 * t := by
                simp only [finish_alternatingPath, Pi.add_apply, Pi.sub_apply,
                  signedBasis_same, signedBasis_of_ne hrp]
                have hsrsq := sq_eq_one_of_natAbs_eq_one sr hsr
                push_cast
                nlinarith
              rw [hycoord, hmiddleR]
            · exact hx
      · have hks : k ≤ s := by
          dsimp [k] at hkt ⊢
          omega
        apply endpoint_far_from_vertices_of_signed_coordinate_gap
          (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
            q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t)
          (exceptionalShortDownwardInnerPath z p r h sp sr sh
            (Ne.symm hrp) hph hrh hsp hsr hsh s t hseparator)
          h sh hsh rsep (sh * z h + t) (k : ℤ)
          (by simpa only [Int.cast_natCast] using hrsep) (by positivity)
        · rw [hordinaryHelper]
          push_cast
          omega
        · intro x hx
          have hbound := exceptionalShortDownwardInnerPath_helper_coordinate_le_finish
            z p r h sp sr sh (Ne.symm hrp) hph hrh hsp hsr hsh
            s t hseparator x hx
          have hef := exceptionalShortDownwardInnerPath_finish_helper_coordinate
            z p r h sp sr sh (Ne.symm hrp) hph hrh hsp hsr hsh
            s t hseparator
          rw [hef] at hbound
          exact hbound
    · have hopposite : boolSign q.1.2 = -sh := by
        rcases Int.natAbs_eq_iff.mp (natAbs_boolSign q.1.2) with hq | hq <;>
        rcases Int.natAbs_eq_iff.mp hsh with hh | hh <;> omega
      have hordinaryHelper : boolSign q.1.2 *
          (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
            q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t).finish h =
          boolSign q.1.2 * z h + s + t := by
        have hof := shortDownwardInnerPath_finish_private_coordinate
          z q.1.1 r p (boolSign q.1.2) sr sp q.2.2 hqp hrp
          (natAbs_boolSign _) hsr hsp s t
        rw [← hqh]
        exact hof
      apply endpoint_far_from_vertices_of_signed_coordinate_gap
        (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
          q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t)
        (exceptionalShortDownwardInnerPath z p r h sp sr sh
          (Ne.symm hrp) hph hrh hsp hsr hsh s t hseparator)
        h (boolSign q.1.2) (natAbs_boolSign _) rsep
        (boolSign q.1.2 * z h) (k : ℤ)
        (by simpa only [Int.cast_natCast] using hrsep) (by positivity)
      · rw [hordinaryHelper]
        push_cast
        have hk : k ≤ s + t := by dsimp [k]; omega
        omega
      · intro x hx
        have hge := exceptionalShortDownwardInnerPath_helper_coordinate_ge_start
          z p r h sp sr sh (Ne.symm hrp) hph hrh hsp hsr hsh
          s t hseparator x hx
        rw [hopposite]
        nlinarith
  · apply endpoint_far_from_vertices_of_signed_coordinate_gap
      (shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
        q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t)
      (exceptionalShortDownwardInnerPath z p r h sp sr sh
        (Ne.symm hrp) hph hrh hsp hsr hsh s t hseparator)
      q.1.1 (boolSign q.1.2) (natAbs_boolSign _) rsep
      (boolSign q.1.2 * z q.1.1) (k : ℤ)
      (by simpa only [Int.cast_natCast] using hrsep) (by positivity)
    · rw [shortDownwardInnerPath_finish_private_coordinate]
      push_cast
      have hk : k ≤ s + t := by dsimp [k]; omega
      omega
    · intro x hx
      have hxcoord := exceptionalShortDownwardInnerPath_other_coordinate
        z p r h sp sr sh (Ne.symm hrp) hph hrh hsp hsr hsh
        s t hseparator x hx q.1.1 hqp q.2.2 hqh
      rw [hxcoord]

end LatticePath

end

end DisjointPaths
