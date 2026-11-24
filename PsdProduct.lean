import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A product inequality for positive semidefinite matrices

Companion to Saigyukari, *A product inequality for positive semidefinite
matrices*. The Fourier identity uses formal power series over ℝ.
The fourth-order differential estimate follows from the density and
scalar differential comparisons in Proposition 4.4.

In a Mathlib v4.36.0 project, run `lake env lean PsdProduct.lean`.
-/

open scoped BigOperators ComplexOrder Matrix MatrixOrder InnerProductSpace Topology ContDiff
open Filter
open Finset

noncomputable section

namespace PsdProduct

/-! ## Diagonal cancellation and congruence -/

/-- The geometric sum with n terms. -/
def geom {R : Type*} [Semiring R] (n : ℕ) (x : R) : R :=
  ∑ k ∈ range n, x ^ k

private lemma geom_succ {R : Type*} [Semiring R] (m : ℕ) (z : R) :
    geom (m + 1) z = geom m z + z ^ m :=
  sum_range_succ _ _

private lemma geom_succ_mul {R : Type*} [Semiring R] (m : ℕ) (z : R) :
    geom (m + 1) z = z * geom m z + 1 :=
  geom_sum_succ

/-- Product over ordered pairs of distinct indices. -/
def offProd {n : ℕ} (f : Fin n → Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ univ.erase i, f i j

/-- Equation (1.2) of the paper. -/
def Cancelled {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  offProd (fun i j => ‖1 - A i j‖) ≤ ∏ i : Fin n, geom n (A i i).re

private lemma diag_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i : Fin n) : 0 ≤ A i i := by
  exact hA.diag_nonneg

private lemma diag_re_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i : Fin n) : 0 ≤ (A i i).re :=
  (Complex.nonneg_iff.mp (diag_nonneg hA i)).1

private lemma diag_real {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i : Fin n) : A i i = ((A i i).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using (Complex.nonneg_iff.mp (diag_nonneg hA i)).2.symm

/-- The Gram Cauchy–Schwarz bound, applied to two columns of a Gram factor. -/
private lemma entry_sq_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i j : Fin n) :
    ‖A i j‖ ^ 2 ≤ (A i i).re * (A j j).re := by
  obtain ⟨D, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  let v (i : Fin n) : EuclideanSpace ℂ (Fin n) :=
    WithLp.toLp 2 (fun k => D k i)
  have gram (i j : Fin n) : ⟪v i, v j⟫_ℂ = (star D * D) i j := by
    simp only [v, EuclideanSpace.inner_toLp_toLp, dotProduct, Matrix.star_eq_conjTranspose,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply, mul_comm]
  have square (i : Fin n) : ‖v i‖ ^ 2 = ((star D * D) i i).re := by
    simpa only [gram, RCLike.re_to_complex] using norm_sq_eq_re_inner (𝕜 := ℂ) (v i)
  rw [← gram i j, ← square i, ← square j, ← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (norm_inner_le_norm (v i) (v j))

private lemma diag_factor {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i : Fin n) :
    ‖1 - A i i ^ m‖ = ‖1 - A i i‖ * geom m (A i i).re := by
  let d := (A i i).re
  have hd : 0 ≤ d := diag_re_nonneg hA i
  have hgeom : 0 ≤ geom m d := sum_nonneg fun _ _ => pow_nonneg hd _
  have hfactor : geom m d * (1 - d) = 1 - d ^ m := geom_sum_mul_neg d m
  rw [show A i i = (d : ℂ) from diag_real hA i]
  -- Keep the real radius fixed when rewriting the complex diagonal.
  simp only [Complex.ofReal_re, ← Complex.ofReal_pow, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, ← hfactor, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg hgeom]
  ring

/-- Multiply the cancelled inequality by the nonnegative diagonal product. -/
theorem of_cancelled {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (h : Cancelled A) :
    (∏ i : Fin n, ∏ j : Fin n, ‖1 - A i j‖) ≤ ∏ i : Fin n, ‖1 - A i i ^ n‖ := by
  have hrows (i : Fin n) :
      (∏ j : Fin n, ‖1 - A i j‖) =
        ‖1 - A i i‖ * ∏ j ∈ univ.erase i, ‖1 - A i j‖ :=
    (mul_prod_erase _ _ (mem_univ i)).symm
  calc
    _ = (∏ i : Fin n, ‖1 - A i i‖) * offProd (fun i j => ‖1 - A i j‖) := by
      simp only [hrows, prod_mul_distrib, offProd]
    _ ≤ (∏ i : Fin n, ‖1 - A i i‖) * ∏ i : Fin n, geom n (A i i).re :=
      mul_le_mul_of_nonneg_left h (prod_nonneg fun _ _ => norm_nonneg _)
    _ = _ := by simp only [diag_factor hA, prod_mul_distrib]

private lemma order_two (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef) :
    Cancelled A := by
  have erase0 : (univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have erase1 : (univ : Finset (Fin 2)).erase 1 = {0} := by decide
  have hnorm : ‖1 - A 1 0‖ = ‖1 - A 0 1‖ := by
    simpa only [star_sub, star_one, hA.isHermitian.apply 1 0] using
      (norm_star (1 - A 0 1))
  have hg (d : ℝ) : geom 2 d = 1 + d := by
    simp [geom, sum_range_succ]
  simp only [Cancelled, offProd, Fin.prod_univ_two, erase0, erase1, prod_singleton, hnorm, hg]
  have h0 := diag_re_nonneg hA 0
  have h1 := diag_re_nonneg hA 1
  have hcs := entry_sq_le hA 0 1
  have hsum : 2 * ‖A 0 1‖ ≤ (A 0 0).re + (A 1 1).re := by
    apply (sq_le_sq₀ (by positivity) (add_nonneg h0 h1)).1
    nlinarith [sq_nonneg ((A 0 0).re - (A 1 1).re)]
  have htri : ‖1 - A 0 1‖ ≤ 1 + ‖A 0 1‖ := by
    simpa only [norm_one] using norm_sub_le (1 : ℂ) (A 0 1)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htri
  nlinarith

/-- The positive diagonal scale tᵢ. -/
def scaleAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ℝ :=
  max 1 (A i i).re

/-- The normalized matrix with entries aᵢⱼ/(tᵢtⱼ). -/
def normalize {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => A i j / ((scaleAt A i * scaleAt A j : ℝ) : ℂ)

private lemma scale_ge_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    1 ≤ scaleAt A i :=
  le_max_left _ _

/-- The normalization is a congruence by a real diagonal matrix. -/
theorem normalize_psd {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    (normalize A).PosSemidef := by
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((scaleAt A i)⁻¹ : ℝ))
  have hD : Dᴴ = D := by
    simp [D, Matrix.diagonal_conjTranspose, Pi.star_apply]
  have hB : D * A * Dᴴ = normalize A := by
    rw [hD]
    apply Matrix.ext
    intro i j
    simp only [D, Matrix.mul_diagonal, Matrix.diagonal_mul, normalize,
      Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  exact hB ▸ hA.mul_mul_conjTranspose_same D

private lemma normalized_diag_le_one_formula {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (hi : (A i i).re ≤ 1) : (normalize A i i).re = (A i i).re := by
  simp [normalize, scaleAt, max_eq_left hi]

private lemma normalized_diag_inv_formula {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (hi : 1 < (A i i).re) : (normalize A i i).re = (A i i).re⁻¹ := by
  have h : (A i i).re ≠ 0 := ne_of_gt (by linarith)
  simp only [normalize, Complex.div_ofReal_re, scaleAt, max_eq_right hi.le]
  field_simp

/-- The normalized diagonals lie in the closed unit interval. -/
theorem normalize_diagonal {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i : Fin n) :
    0 ≤ (normalize A i i).re ∧ (normalize A i i).re ≤ 1 := by
  refine ⟨diag_re_nonneg (normalize_psd hA) i, ?_⟩
  by_cases hi : (A i i).re ≤ 1
  · rwa [normalized_diag_le_one_formula A i hi]
  · have hd : 1 < (A i i).re := lt_of_not_ge hi
    rw [normalized_diag_inv_formula A i hd]
    exact (inv_lt_one_of_one_lt₀ hd).le

/-- For a matrix with no unit diagonal entry the normalized diagonals are strictly below 1. -/
private lemma normalize_lt_one {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hn : ∀ i : Fin n, (A i i).re ≠ 1) (i : Fin n) : (normalize A i i).re < 1 := by
  rcases lt_or_gt_of_ne (hn i) with hi | hi
  · rwa [normalized_diag_le_one_formula A i hi.le]
  · rw [normalized_diag_inv_formula A i hi]
    exact inv_lt_one_of_one_lt₀ hi

private lemma geom_reverse {d : ℝ} (hd : d ≠ 0) (n : ℕ) :
    geom n d = d ^ (n - 1) * geom n d⁻¹ := by
  have reversal (m : ℕ) : geom (m + 1) d = d ^ m * geom (m + 1) d⁻¹ := by
    induction m with
    | zero => simp [geom]
    | succ m ih =>
      calc
        geom (m + 1 + 1) d = geom (m + 1) d + d ^ (m + 1) := geom_succ _ _
        _ = d ^ m * geom (m + 1) d⁻¹ + d ^ (m + 1) := by rw [ih]
        _ = d ^ (m + 1) * (d⁻¹ * geom (m + 1) d⁻¹ + 1) := by
          rw [pow_succ]
          field_simp [hd]
        _ = _ := by rw [geom_succ_mul (m + 1) d⁻¹]
  cases n with
  | zero => simp [geom]
  | succ m => exact reversal m

private lemma diag_scale {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    geom n (A i i).re = scaleAt A i ^ (n - 1) * geom n (normalize A i i).re := by
  by_cases hi : (A i i).re ≤ 1
  · simp [normalized_diag_le_one_formula A i hi, scaleAt, max_eq_left hi]
  · have hd : 1 < (A i i).re := lt_of_not_ge hi
    rw [normalized_diag_inv_formula A i hd, scaleAt, max_eq_right hd.le]
    exact geom_reverse (ne_of_gt (by linarith)) n

private lemma pair_scale (z : ℂ) {T : ℝ} (hT : 1 ≤ T) (hz : ‖z‖ ^ 2 ≤ T) :
    ‖1 - z‖ ^ 2 ≤ T * ‖1 - z / (T : ℂ)‖ ^ 2 := by
  have hpos : 0 < T := by linarith
  have halg :
      T * ‖1 - z / (T : ℂ)‖ ^ 2 - ‖1 - z‖ ^ 2 =
        (T - 1) * (1 - ‖z‖ ^ 2 / T) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.div_ofReal_re, Complex.div_ofReal_im]
    field_simp
    ring
  have hnonneg : 0 ≤ (T - 1) * (1 - ‖z‖ ^ 2 / T) :=
    mul_nonneg (sub_nonneg.mpr hT) (sub_nonneg.mpr ((div_le_one hpos).2 hz))
  linarith

private lemma offProd_mul {n : ℕ} (f g : Fin n → Fin n → ℝ) :
    offProd (fun i j => f i j * g i j) = offProd f * offProd g := by
  simp only [offProd, prod_mul_distrib]

private lemma offProd_pow {n : ℕ} (f : Fin n → Fin n → ℝ) (k : ℕ) :
    offProd (fun i j => f i j ^ k) = offProd f ^ k := by
  simp only [offProd, ← prod_pow]

private lemma offProd_swap {n : ℕ} (f : Fin n → Fin n → ℝ) :
    offProd (fun i j => f j i) = offProd f := by
  unfold offProd
  exact prod_comm' (fun _ _ => by simp [ne_comm])

private lemma offProd_row {n : ℕ} (t : Fin n → ℝ) :
    offProd (fun i _ => t i) = ∏ i : Fin n, t i ^ (n - 1) := by
  simp [offProd, card_erase_of_mem]

private lemma offProd_weights {n : ℕ} (t : Fin n → ℝ) :
    offProd (fun i j => t i * t j) = (∏ i : Fin n, t i ^ (n - 1)) ^ 2 := by
  rw [offProd_mul, offProd_swap (fun i _ => t i), offProd_row]
  ring

/-- Transport (1.2) from the congruence-normalized matrix back to the original. -/
theorem cancelled_of_normalize {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : Cancelled (normalize A)) : Cancelled A := by
  let t := scaleAt A
  let f := fun i j => ‖1 - A i j‖
  let g := fun i j => ‖1 - normalize A i j‖
  let T := ∏ i : Fin n, t i ^ (n - 1)
  have ht (i : Fin n) : 1 ≤ t i := scale_ge_one A i
  have ht0 (i : Fin n) : 0 ≤ t i := (zero_le_one : (0 : ℝ) ≤ 1).trans (ht i)
  have hT0 : 0 ≤ T := prod_nonneg fun i _ => pow_nonneg (ht0 i) _
  have hij (i j : Fin n) : f i j ^ 2 ≤ t i * t j * g i j ^ 2 := by
    have hscale : 1 ≤ t i * t j := one_le_mul_of_one_le_of_one_le (ht i) (ht j)
    have he : ‖A i j‖ ^ 2 ≤ t i * t j := (entry_sq_le hA i j).trans
      (mul_le_mul (le_max_right _ _) (le_max_right _ _) (diag_re_nonneg hA j) (ht0 i))
    exact pair_scale (A i j) hscale he
  have hprod :
      offProd (fun i j => f i j ^ 2) ≤ offProd (fun i j => (t i * t j) * g i j ^ 2) :=
    prod_le_prod₀ (fun _ _ => prod_nonneg fun _ _ => sq_nonneg _)
      (fun i _ => prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun j _ => hij i j))
  rw [offProd_mul, offProd_weights, offProd_pow, offProd_pow, ← mul_pow] at hprod
  have hf : offProd f ≤ T * offProd g :=
    (sq_le_sq₀
      (prod_nonneg fun _ _ => prod_nonneg fun _ _ => norm_nonneg _)
      (mul_nonneg hT0 (prod_nonneg fun _ _ => prod_nonneg fun _ _ => norm_nonneg _))).1 hprod
  calc
    offProd f ≤ T * offProd g := hf
    _ ≤ T * ∏ i : Fin n, geom n (normalize A i i).re := mul_le_mul_of_nonneg_left hB hT0
    _ = ∏ i : Fin n, geom n (A i i).re := by
      dsimp only [T, t]
      rw [← prod_mul_distrib]
      exact prod_congr rfl (fun i _ => (diag_scale A i).symm)

/-! ## The Fourier identity

A formal power series with real coefficients stores the one-sided coefficients.
The geometric squares satisfy a second-difference formula and the cosine
sequence satisfies its order-two recurrence. Their generating series turn
the two summations by parts in identity (A) into polynomial multiplication.
-/

/-- L_m, with its separately specified endpoint L_0 = 0. -/
def auxiliary (U : ℕ → ℝ) (C : ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => (U (m + 2) + U m) / 2 - C * U (m + 1)

/-- The paper's B_{j+1}, indexed here by j starting at 0. -/
def fejerWeight (U : ℕ → ℝ) (C : ℝ) (j : ℕ) : ℝ :=
  auxiliary U C (j + 1) - 2 * auxiliary U C j + auxiliary U C (j - 1)

private def cosine (z : ℂ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => 2 * (z ^ (k + 1)).re

/-- U_n h_n on the circle. For U₀=U₁=0, the frequencies n−1 and n vanish. -/
def fourierNumerator (U : ℕ → ℝ) (z : ℂ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, U (j + 1) * cosine z (n - 1 - j)

private def squareSum (z : ℂ) (j : ℕ) : ℝ := Complex.normSq (geom j z)

private lemma squareSum_succ (z : ℂ) (hz : Complex.normSq z = 1) (m : ℕ) :
    squareSum z (m + 1) = squareSum z m + 1 + 2 * (z * geom m z).re := by
  rw [squareSum, geom_succ_mul, Complex.normSq_add, Complex.normSq_mul, hz, one_mul]
  simp [squareSum]

private lemma squareSum_second (z : ℂ) (hz : Complex.normSq z = 1) (m : ℕ) :
    squareSum z (m + 2) - 2 * squareSum z (m + 1) + squareSum z m =
      2 * (z ^ (m + 1)).re := by
  have h : (z * geom (m + 1) z).re = (z * geom m z).re + (z ^ (m + 1)).re := by
    rw [geom_succ, mul_add, Complex.add_re, pow_succ']
  linarith [squareSum_succ z hz m, squareSum_succ z hz (m + 1)]

private lemma re_power_recurrence (z : ℂ) (hz : Complex.normSq z = 1) (m : ℕ) :
    (z ^ (m + 2)).re + (z ^ m).re = 2 * z.re * (z ^ (m + 1)).re := by
  have hz' : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hz, Complex.ofReal_one]
  have h : z ^ (m + 2) + z ^ m = (z + star z) * z ^ (m + 1) := by
    calc
      _ = z * z ^ (m + 1) + z ^ m * (z * star z) := by rw [hz', mul_one, ← pow_succ']
      _ = _ := by rw [pow_succ' z m]; ring
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.add_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im] at hr
  linarith

private abbrev Series := PowerSeries ℝ
private abbrev Xs : Series := PowerSeries.X
private abbrev coeff := PowerSeries.coeff (R := ℝ)
private abbrev const := PowerSeries.C (R := ℝ)
private abbrev series (f : ℕ → ℝ) : Series := PowerSeries.mk f

private def recursionPoly (r : ℝ) : Series := 1 - const (2 * r) * Xs + Xs ^ 2

private lemma coeff_X (F : Series) (m : ℕ) :
    coeff m (Xs * F) = if 1 ≤ m then coeff (m - 1) F else 0 := by
  simpa only [pow_one] using PowerSeries.coeff_X_pow_mul' F 1 m

private lemma recursion_coeff (r : ℝ) (F : Series) (m : ℕ) :
    coeff m (recursionPoly r * F) =
      coeff m F - 2 * r * (if 1 ≤ m then coeff (m - 1) F else 0) +
        (if 2 ≤ m then coeff (m - 2) F else 0) := by
  rw [recursionPoly, add_mul, sub_mul, one_mul, mul_assoc]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X,
    PowerSeries.coeff_X_pow_mul']

private lemma squares_series (z : ℂ) (hz : Complex.normSq z = 1) :
    recursionPoly 1 * series (fun j => squareSum z (j + 1)) = series (cosine z) := by
  apply PowerSeries.ext
  intro m
  rw [recursion_coeff]
  rcases m with _ | _ | m
  · simp [squareSum, geom, cosine]
  · have hs := squareSum_succ z hz 1
    simp [squareSum, geom, sum_range_succ] at hs
    simp [cosine, squareSum, geom, sum_range_succ]
    linarith
  · have hs := squareSum_second z hz (m + 1)
    simp [cosine] at *
    linarith

private lemma cosine_series (z : ℂ) (hz : Complex.normSq z = 1) :
    recursionPoly z.re * series (cosine z) = 1 - Xs ^ 2 := by
  apply PowerSeries.ext
  intro m
  rw [recursion_coeff, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  rcases m with _ | _ | _ | m
  · norm_num [cosine]
  · norm_num [cosine]
  · have hr := re_power_recurrence z hz 0
    norm_num [cosine] at hr ⊢
    linarith
  · have hr := re_power_recurrence z hz (m + 1)
    simp [cosine] at *
    linarith

private lemma auxiliary_series (U : ℕ → ℝ) (C : ℝ) (h0 : U 0 = 0) (h1 : U 1 = 0) :
    const 2 * (Xs * series (fun j => auxiliary U C (j + 1))) =
      recursionPoly C * series (fun j => U (j + 1)) := by
  apply PowerSeries.ext
  intro m
  rw [PowerSeries.coeff_C_mul, coeff_X, recursion_coeff]
  rcases m with _ | _ | m <;> simp [auxiliary, h0, h1] <;> ring

private lemma weights_series (U : ℕ → ℝ) (C : ℝ) :
    series (fejerWeight U C) = recursionPoly 1 * series (fun j => auxiliary U C (j + 1)) := by
  apply PowerSeries.ext
  intro m
  rw [recursion_coeff]
  rcases m with _ | _ | m <;> simp [fejerWeight, auxiliary]

private lemma coeff_series_product (f g : ℕ → ℝ) (m : ℕ) :
    coeff m (series f * series g) = ∑ j ∈ range (m + 1), f j * g (m - j) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]

/-- Identity (A), with the Poisson and Fourier denominators cleared. The
parameters C and T stand for cosh c and M sinh c, respectively. -/
theorem fourier_sos (U : ℕ → ℝ) (C T : ℝ) {n : ℕ} (hn : 3 ≤ n)
    (h0 : U 0 = 0) (h1 : U 1 = 0) (z : ℂ) (hz : ‖z‖ = 1) :
    T * U n - (C - z.re) * fourierNumerator U z n =
      T * U n - (U (n + 1) - U (n - 1)) / 2 +
        ∑ j ∈ range n, fejerWeight U C j * ‖geom (n - j) z‖ ^ 2 := by
  have hzSq : Complex.normSq z = 1 := by rw [← Complex.sq_norm, hz, one_pow]
  let V := series (fun j => U (j + 1))
  let K := series (cosine z)
  let G := series (fun j => squareSum z (j + 1))
  let L := series (fun j => auxiliary U C (j + 1))
  let B := series (fejerWeight U C)
  have he : recursionPoly C = recursionPoly z.re + const (2 * (z.re - C)) * Xs := by
    simp only [recursionPoly, mul_sub, map_sub]
    ring
  have hs :
      const 2 * (Xs * (B * G)) =
        (1 - Xs ^ 2) * V + const (2 * (z.re - C)) * (Xs * (V * K)) := by
    calc
      _ = (const 2 * (Xs * L)) * (recursionPoly 1 * G) := by
        rw [show B = recursionPoly 1 * L from weights_series U C]
        ring
      _ = (recursionPoly C * V) * K := by
        rw [show const 2 * (Xs * L) = recursionPoly C * V from auxiliary_series U C h0 h1,
          show recursionPoly 1 * G = K from squares_series z hzSq]
      _ = (recursionPoly z.re * K) * V + const (2 * (z.re - C)) * (Xs * (V * K)) := by
        rw [he]
        ring
      _ = _ := by rw [show recursionPoly z.re * K = 1 - Xs ^ 2 from cosine_series z hzSq]
  have hcoef := congrArg (coeff n) hs
  have hN1 : 1 ≤ n := by omega
  have hN2 : 2 ≤ n := by omega
  have hRange : n - 1 + 1 = n := by omega
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X,
    PowerSeries.coeff_X_pow_mul', sub_mul, one_mul, ite_eq_left hN1, ite_eq_left hN2,
    V, K, B, G, PowerSeries.coeff_mk, coeff_series_product, hRange] at hcoef
  have hindex (j : ℕ) (hj : j ∈ range n) : n - 1 - j + 1 = n - j := by
    have := mem_range.mp hj
    omega
  have hSqSum :
      (∑ j ∈ range n, fejerWeight U C j * squareSum z (n - 1 - j + 1)) =
        ∑ j ∈ range n, fejerWeight U C j * ‖geom (n - j) z‖ ^ 2 := by
    apply sum_congr rfl
    intro j hj
    rw [hindex j hj, squareSum, Complex.sq_norm]
  rw [hSqSum, show n - 2 + 1 = n - 1 by omega] at hcoef
  change _ = _ + 2 * (z.re - C) * fourierNumerator U z n at hcoef
  linarith

/-! ## Logarithmic radii and hyperbolic endpoint bounds -/

private def H (q s : ℝ) : ℝ := Real.sinh (s * q) - s * Real.sinh q

/-- The signed branch across s = 1 agrees with the analytic extension of
the positive square root on s ≥ 1. -/
def radialU (a b s : ℝ) : ℝ :=
  if s < 1 then -Real.sqrt (H a s * H b s) else Real.sqrt (H a s * H b s)

private def radii (a b : ℝ) (m : ℕ) : ℝ := radialU a b m
private def midpoint (a b : ℝ) : ℝ := (a + b) / 2
private def logWeight (n : ℕ) (q : ℝ) : ℝ := (Real.cosh (n * q) - 1) / H q n
private def meanTerm (n : ℕ) (a b : ℝ) : ℝ :=
  Real.sqrt (logWeight n a * logWeight n b) * Real.sinh (midpoint a b)

private def differential (a b s : ℝ) : ℝ :=
  iteratedDeriv 4 (radialU a b) s - midpoint a b ^ 2 * iteratedDeriv 2 (radialU a b) s

private def triangular (u : ℝ) : ℝ := 1 - |u|
private def green (c v : ℝ) : ℝ := Real.sinh (c * (1 - |v|)) / c

private lemma H_deriv_q (s q : ℝ) :
    HasDerivAt (fun x => H x s) (s * (Real.cosh (s * q) - Real.cosh q)) q := by
  have h := (((hasDerivAt_id q).const_mul s).sinh).sub
    ((Real.hasDerivAt_sinh q).const_mul s)
  convert h using 1
  · rfl
  · simp only [id_eq, mul_one]
    ring

private lemma H_deriv_s (q s : ℝ) :
    HasDerivAt (H q) (q * Real.cosh (s * q) - Real.sinh q) s := by
  have h := (((hasDerivAt_id s).mul_const q).sinh).sub
    ((hasDerivAt_id s).mul_const (Real.sinh q))
  convert h using 1
  · rfl
  · simp only [id_eq, one_mul]
    ring

private lemma H_pos {q s : ℝ} (hq : 0 < q) (hs : 1 < s) : 0 < H q s := by
  have hm : StrictMonoOn (fun x => H x s) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr (fun x => (H_deriv_q s x).continuousAt)).continuousOn
    · intro x hx
      have hx0 : 0 < x := by simpa using hx
      rw [(H_deriv_q s x).deriv]
      apply mul_pos (by linarith)
      apply sub_pos.mpr
      rw [Real.cosh_lt_cosh, abs_of_pos hx0, abs_of_pos (by positivity)]
      nlinarith
  simpa [H] using hm (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hq.le) hq

private lemma sinh_mul_sub_pos {q : ℝ} (hq : 0 < q) :
    0 < q * Real.cosh q - Real.sinh q := by
  let F (x : ℝ) := x * Real.cosh x - Real.sinh x
  have hF (x : ℝ) : HasDerivAt F (x * Real.sinh x) x := by
    convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x) using 1
    · rfl
    · simp only [id_eq, one_mul]
      ring
  have hm : StrictMonoOn F (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr (fun x => (hF x).continuousAt)).continuousOn
    · intro x hx
      have h : 0 < x := by simpa using hx
      rw [(hF x).deriv]
      exact mul_pos h (Real.sinh_pos_iff.mpr h)
  simpa [F] using hm (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hq.le) hq

private lemma radii_sq (a b : ℝ) {m : ℕ} (ha : 0 < a) (hb : 0 < b) (hm : 2 ≤ m) :
    radii a b m ^ 2 = H a m * H b m := by
  have hm' : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  simp [radii, radialU, not_lt.mpr hm'.le, Real.sq_sqrt (mul_nonneg
    (H_pos ha hm').le (H_pos hb hm').le)]

private lemma radii_nonneg (a b : ℝ) {m : ℕ} (hm : 1 ≤ m) : 0 ≤ radii a b m := by
  have h : (1 : ℝ) ≤ m := by exact_mod_cast hm
  simp [radii, radialU, not_lt.mpr h, Real.sqrt_nonneg]

private lemma H_three (q : ℝ) : H q 3 = 2 * (1 + Real.cosh q) * H q 2 := by
  rw [H, H, Real.sinh_three_mul, Real.sinh_two_mul]
  linear_combination 4 * Real.sinh q * Real.sinh_sq q

private lemma H_four (q : ℝ) :
    H q 4 = 2 * (Real.cosh q ^ 2 + (1 + Real.cosh q) ^ 2) * H q 2 := by
  rw [H, H, show (4 : ℝ) * q = 2 * (2 * q) by ring, Real.sinh_two_mul,
    Real.cosh_two_mul, Real.sinh_two_mul, Real.sinh_sq]
  ring

/-- Lemma 4.2. The first three coefficients involve the endpoint of the
sequence and follow from the double- and triple-angle formulas. -/
private theorem first_weights (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ j < 3, 0 ≤ fejerWeight (radii a b) (Real.cosh (midpoint a b)) j := by
  let U := radii a b
  let c := midpoint a b
  let d := (a - b) / 2
  let C := Real.cosh c
  let D := Real.cosh d
  let A := Real.cosh a
  let B := Real.cosh b
  have hC : 1 ≤ C := Real.one_le_cosh _
  have hD : 1 ≤ D := Real.one_le_cosh _
  have hA : 1 ≤ A := Real.one_le_cosh _
  have hB : 1 ≤ B := Real.one_le_cosh _
  have aeq : Real.cosh a = C * D + Real.sinh c * Real.sinh d := by
    have he : a = c + d := by unfold c d midpoint; ring
    rw [he, Real.cosh_add]
  have beq : Real.cosh b = C * D - Real.sinh c * Real.sinh d := by
    have he : b = c - d := by unfold c d midpoint; ring
    rw [he, Real.cosh_sub]
  have hadd : A + B = 2 * C * D := by dsimp only [A, B]; rw [aeq, beq]; ring
  have hmul : A * B = C ^ 2 + D ^ 2 - 1 := by
    dsimp only [A, B]
    rw [aeq, beq, show (C * D + Real.sinh c * Real.sinh d) *
      (C * D - Real.sinh c * Real.sinh d) =
        C ^ 2 * D ^ 2 - Real.sinh c ^ 2 * Real.sinh d ^ 2 by ring]
    rw [Real.sinh_sq, Real.sinh_sq]
    change C ^ 2 * D ^ 2 - (C ^ 2 - 1) * (D ^ 2 - 1) = _
    ring
  have hsq : (C + D) ^ 2 = (1 + A) * (1 + B) := by
    nlinarith only [hadd, hmul]
  have h0 : U 0 = 0 := by simp [U, radii, radialU, H]
  have h1 : U 1 = 0 := by simp [U, radii, radialU, H]
  have h2 : 0 ≤ U 2 := radii_nonneg _ _ (by decide)
  have h3 : U 3 = 2 * (C + D) * U 2 := by
    apply (sq_eq_sq₀ (radii_nonneg _ _ (by decide)) (by positivity)).1
    rw [show U 3 ^ 2 = H a 3 * H b 3 from radii_sq a b ha hb (m := 3) (by decide),
      H_three, H_three, mul_pow, mul_pow,
      show U 2 ^ 2 = H a 2 * H b 2 from radii_sq a b ha hb (m := 2) (by decide), hsq]
    change 2 * (1 + A) * H a 2 * (2 * (1 + B) * H b 2) =
      2 ^ 2 * ((1 + A) * (1 + B)) * (H a 2 * H b 2)
    ring
  let V := A * B + (1 + A) * (1 + B)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hVeq : V = 2 * C ^ 2 + 2 * D ^ 2 + 2 * C * D - 1 := by
    dsimp [V]
    nlinarith only [hadd, hmul]
  have h4 : 2 * V * U 2 ≤ U 4 := by
    apply (sq_le_sq₀ (by positivity) (radii_nonneg _ _ (by decide))).1
    rw [show U 4 ^ 2 = H a 4 * H b 4 from radii_sq a b ha hb (m := 4) (by decide),
      H_four, H_four, mul_pow, mul_pow,
      show U 2 ^ 2 = H a 2 * H b 2 from radii_sq a b ha hb (m := 2) (by decide)]
    change 2 ^ 2 * V ^ 2 * (H a 2 * H b 2) ≤
      2 * (A ^ 2 + (1 + A) ^ 2) * H a 2 * (2 * (B ^ 2 + (1 + B) ^ 2) * H b 2)
    have hcs : V ^ 2 ≤ (A ^ 2 + (1 + A) ^ 2) * (B ^ 2 + (1 + B) ^ 2) := by
      dsimp [V]
      nlinarith only [sq_nonneg (A - B)]
    calc
      _ ≤ 2 ^ 2 * ((A ^ 2 + (1 + A) ^ 2) * (B ^ 2 + (1 + B) ^ 2)) *
          (H a 2 * H b 2) := by
        gcongr
        exact mul_nonneg (H_pos ha (by norm_num)).le (H_pos hb (by norm_num)).le
      _ = _ := by ring
  change ∀ j < 3, 0 ≤ fejerWeight U C j
  intro j hj
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl | rfl
  · norm_num [fejerWeight, auxiliary, h0, h1]
    positivity
  · norm_num [fejerWeight, auxiliary, h0, h1, h3]
    nlinarith only [mul_nonneg h2 (sub_nonneg.mpr hD)]
  · norm_num [fejerWeight, auxiliary, h0, h1, h3]
    rw [hVeq] at h4
    have hp : 0 ≤ 2 * U 2 * D * (D - 1) := by positivity
    linarith only [h4, hp]

/-! Complete homogeneous coefficients. Adjoining a variable x replaces the
coefficient sequence f by the coefficients of f(X)/(1 - xX). -/

private def adjoin (x : ℝ) (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | m + 1 => f (m + 1) + x * adjoin x f m

private def generator (x : ℝ) : Series := 1 - const x * Xs

private lemma generator_coeff (x : ℝ) (F : Series) (m : ℕ) :
    coeff m (generator x * F) =
      coeff m F - x * (if 1 ≤ m then coeff (m - 1) F else 0) := by
  simp only [generator, sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, coeff_X]

private lemma adjoin_series (x : ℝ) (f : ℕ → ℝ) :
    generator x * series (adjoin x f) = series f := by
  apply PowerSeries.ext
  intro m
  cases m <;> simp [generator_coeff, adjoin]

private lemma generator_cancel (x : ℝ) {F G : Series}
    (h : generator x * F = generator x * G) : F = G := by
  apply PowerSeries.ext
  intro m
  have eq (k : ℕ) := congrArg (coeff k) h
  induction m with
  | zero => simpa [generator_coeff] using eq 0
  | succ m ih =>
    simpa [generator_coeff, ih] using eq (m + 1)

private lemma adjoin_swap (x y : ℝ) (f : ℕ → ℝ) :
    adjoin x (adjoin y f) = adjoin y (adjoin x f) := by
  have h₁ : generator x * generator y * series (adjoin x (adjoin y f)) = series f := by
    rw [mul_comm (generator x), mul_assoc, adjoin_series, adjoin_series]
  have h₂ : generator x * generator y * series (adjoin y (adjoin x f)) = series f := by
    rw [mul_assoc, adjoin_series, adjoin_series]
  have h := h₁.trans h₂.symm
  rw [mul_assoc, mul_assoc] at h
  have h' := generator_cancel y (generator_cancel x h)
  funext m
  simpa only [PowerSeries.coeff_mk] using congrArg (coeff m) h'

private def LogConcaveSeq (f : ℕ → ℝ) : Prop :=
  ∀ m, f (m + 2) * f m ≤ f (m + 1) ^ 2

private lemma adjoin_pos {x : ℝ} (hx : 0 ≤ x) {f : ℕ → ℝ} (hf : ∀ m, 0 < f m) :
    ∀ m, 0 < adjoin x f m := by
  intro m
  induction m with
  | zero => exact hf 0
  | succ m ih => exact add_pos_of_pos_of_nonneg (hf _) (mul_nonneg hx ih.le)

private lemma adjoin_cross {x : ℝ} (hx : 0 ≤ x) {f : ℕ → ℝ}
    (hf : ∀ m, 0 < f m) (hl : LogConcaveSeq f) (m : ℕ) :
    f (m + 2) * adjoin x f m ≤ f (m + 1) * adjoin x f (m + 1) := by
  induction m with
  | zero =>
    have h := hl 0
    have hp := mul_nonneg (hf 1).le (mul_nonneg hx (hf 0).le)
    simp only [adjoin]
    nlinarith only [h, hp]
  | succ m ih =>
    have h₁ := mul_le_mul_of_nonneg_right (hl (m + 1)) (adjoin_pos hx hf m).le
    have h₂ := mul_le_mul_of_nonneg_left ih (hf (m + 2)).le
    have h₃ : f (m + 3) * adjoin x f m ≤ f (m + 2) * adjoin x f (m + 1) := by
      apply le_of_mul_le_mul_left ?_ (hf (m + 1))
      nlinarith only [h₁, h₂]
    have h₄ := mul_le_mul_of_nonneg_left h₃ hx
    change _ * (f (m + 1) + x * adjoin x f m) ≤
      _ * (f (m + 2) + x * adjoin x f (m + 1))
    nlinarith only [hl (m + 1), h₄]

private lemma adjoin_logConcave {x : ℝ} (hx : 0 ≤ x) {f : ℕ → ℝ}
    (hf : ∀ m, 0 < f m) (hl : LogConcaveSeq f) : LogConcaveSeq (adjoin x f) := by
  intro m
  have h := adjoin_cross hx hf hl m
  rw [show adjoin x f (m + 2) = f (m + 2) + x * adjoin x f (m + 1) by rfl,
    show (adjoin x f (m + 1)) ^ 2 =
      (f (m + 1) + x * adjoin x f m) * adjoin x f (m + 1) by rw [← adjoin, sq]]
  nlinarith only [h]

/-- Successive complete homogeneous coefficient ratios increase in each variable.
This proof uses only the two-term recurrence for adjoining a variable. -/
private lemma adjoin_ratio {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {f : ℕ → ℝ}
    (hf : ∀ m, 0 < f m) (hl : LogConcaveSeq f) (m : ℕ) :
    adjoin x f (m + 1) / adjoin x f m ≤ adjoin y f (m + 1) / adjoin y f m := by
  have hy := hx.trans hxy
  rw [div_le_div_iff₀ (adjoin_pos hx hf _) (adjoin_pos hy hf _)]
  have aux (k : ℕ) : f (k + 1) * (adjoin y f k - adjoin x f k) ≤
      (y - x) * adjoin y f k * adjoin x f k := by
    induction k with
    | zero =>
      simp only [adjoin, sub_self, mul_zero]
      exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hxy) (hf 0).le) (hf 0).le
    | succ k ih =>
      have h := adjoin_cross hy hf hl k
      have hdiff := sub_nonneg.mpr hxy
      have hp := (adjoin_pos hx hf k).le
      have h₁ := mul_le_mul_of_nonneg_left h hdiff
      have h₂ := mul_le_mul_of_nonneg_right h₁ hp
      have h₃ := mul_le_mul_of_nonneg_left ih (hf (k + 2)).le
      have h₄ : f (k + 2) * (adjoin y f k - adjoin x f k) ≤
          (y - x) * adjoin y f (k + 1) * adjoin x f k := by
        apply le_of_mul_le_mul_left ?_ (hf (k + 1))
        nlinarith only [h₂, h₃]
      have h₅ := mul_le_mul_of_nonneg_left h₄ hx
      rw [show adjoin y f (k + 1) - adjoin x f (k + 1) =
          (y - x) * adjoin y f k + x * (adjoin y f k - adjoin x f k) by
        rw [adjoin, adjoin]; ring]
      rw [show adjoin x f (k + 1) = f (k + 1) + x * adjoin x f k by rfl]
      nlinarith only [h₁, h₅]
  rw [show adjoin x f (m + 1) = f (m + 1) + x * adjoin x f m by rfl,
    show adjoin y f (m + 1) = f (m + 1) + y * adjoin y f m by rfl]
  nlinarith only [aux m]

private def hom (x y z t : ℝ) : ℕ → ℝ :=
  adjoin x (adjoin y (adjoin z (fun j => t ^ j)))

private lemma geom_pos (t : ℝ) (ht : 0 < t) : ∀ m : ℕ, 0 < t ^ m := fun _ => pow_pos ht _
private lemma geom_lc (t : ℝ) : LogConcaveSeq (fun m : ℕ => t ^ m) := by
  intro m
  rw [← pow_add, ← pow_mul, show m + 2 + m = (m + 1) * 2 by omega]

private lemma hom_pos {x y z t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 < t) :
    ∀ m, 0 < hom x y z t m :=
  adjoin_pos hx (adjoin_pos hy (adjoin_pos hz (geom_pos t ht)))

private lemma hom_first_ratio {x x' y z t : ℝ} (hx : 0 ≤ x) (hxx' : x ≤ x')
    (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 < t) (m : ℕ) :
    hom x y z t (m + 2) / hom x y z t m ≤ hom x' y z t (m + 2) / hom x' y z t m := by
  have hl := adjoin_logConcave hy (adjoin_pos hz (geom_pos t ht))
    (adjoin_logConcave hz (geom_pos t ht) (geom_lc t))
  have hp := adjoin_pos hy (adjoin_pos hz (geom_pos t ht))
  have h₁ := adjoin_ratio hx hxx' hp hl m
  have h₂ := adjoin_ratio hx hxx' hp hl (m + 1)
  have he (u : ℝ) (hu : 0 ≤ u) :
      hom u y z t (m + 2) / hom u y z t m =
        hom u y z t (m + 2) / hom u y z t (m + 1) *
          (hom u y z t (m + 1) / hom u y z t m) := by
    field_simp [(hom_pos hu hy hz ht (m + 1)).ne']
  rw [he x hx, he x' (hx.trans hxx')]
  exact mul_le_mul h₂ h₁ (div_pos (hom_pos hx hy hz ht _) (hom_pos hx hy hz ht _)).le
    (div_pos (hom_pos (hx.trans hxx') hy hz ht _) (hom_pos (hx.trans hxx') hy hz ht _)).le

private lemma hom_scale (u x y z t : ℝ) (m : ℕ) :
    hom (u * x) (u * y) (u * z) (u * t) m = u ^ m * hom x y z t m := by
  have aux (d : ℝ) (f : ℕ → ℝ) :
      adjoin (u * d) (fun j => u ^ j * f j) = fun k => u ^ k * adjoin d f k := by
    funext k
    induction k with
    | zero => simp [adjoin]
    | succ k ih => simp only [adjoin, ih, pow_succ]; ring
  simp only [hom, mul_pow, aux]

private lemma generator_geom (x : ℝ) :
    generator x * series (fun j => x ^ j) = 1 := by
  apply PowerSeries.ext
  intro j
  cases j with
  | zero => simp [generator_coeff]
  | succ j => rw [generator_coeff]; simp [pow_succ']

private lemma generator_increasing :
    generator 1 ^ 2 * series (fun j => (j : ℝ)) = Xs := by
  apply PowerSeries.ext
  intro m
  rw [pow_two, mul_assoc, generator_coeff]
  rcases m with _ | _ | m <;> simp [generator_coeff, PowerSeries.coeff_X]

private lemma generator_sinh (q : ℝ) :
    (generator (Real.exp q) * generator (Real.exp (-q))) *
      series (fun m => Real.sinh ((m : ℝ) * q)) = const (Real.sinh q) * Xs := by
  have he : generator (Real.exp q) * generator (Real.exp (-q)) =
      recursionPoly (Real.cosh q) := by
    have hsum : Real.exp q + Real.exp (-q) = 2 * Real.cosh q := by
      rw [Real.cosh_eq]; ring
    have hmul : Real.exp q * Real.exp (-q) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    simp only [generator, recursionPoly]
    calc
      _ = 1 - const (Real.exp q + Real.exp (-q)) * Xs +
        const (Real.exp q * Real.exp (-q)) * Xs ^ 2 := by
        simp only [map_add, map_mul]; ring
      _ = _ := by rw [hsum, hmul, map_one, one_mul]
  rw [he]
  apply PowerSeries.ext
  intro m
  rw [recursion_coeff, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  rcases m with _ | _ | m
  · norm_num
  · norm_num
  · have hc : Real.sinh ((↑m + 2) * q) + Real.sinh ((m : ℝ) * q) =
        2 * Real.cosh q * Real.sinh ((↑m + 1) * q) := by
      rw [show ((↑m + 2) : ℝ) * q = ((↑m + 1) : ℝ) * q + q by ring,
        show (m : ℝ) * q = ((↑m + 1) : ℝ) * q - q by ring, Real.sinh_add, Real.sinh_sub]
      ring
    simp
    simpa only [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring] using
      (show Real.sinh ((↑m + 2) * q) - 2 * Real.cosh q * Real.sinh ((↑m + 1) * q) +
        Real.sinh ((m : ℝ) * q) = 0 by linarith only [hc])

/-- The generating function for H_m, with four geometric factors. -/
private lemma H_hom (q : ℝ) (m : ℕ) :
    H q (m + 2) = H q 2 * hom (Real.exp q) 1 1 (Real.exp (-q)) m := by
  let A := generator (Real.exp q)
  let B := generator (Real.exp (-q))
  let G := generator 1
  let L := series (fun m => H q (m + 2))
  let T := series (fun m => Real.sinh ((m : ℝ) * q))
  let N := series (fun m => (m : ℝ))
  let P := A * G * G * B
  have hH : Xs ^ 2 * L = T - const (Real.sinh q) * N := by
    apply PowerSeries.ext
    intro j
    rw [PowerSeries.coeff_X_pow_mul', map_sub, PowerSeries.coeff_C_mul]
    rcases j with _ | _ | j
    · simp [T, N]
    · simp [T, N]
    · simp only [L, T, N, H, PowerSeries.coeff_mk, Nat.cast_succ, le_add_self, ite_eq_left]
      norm_num
      rw [show (j : ℝ) + 1 + 1 = j + 2 by ring]
      ring
  have hG : G ^ 2 * N = Xs := generator_increasing
  have hS : A * B * T = const (Real.sinh q) * Xs := generator_sinh q
  have hdif : G ^ 2 - A * B = const (2 * (Real.cosh q - 1)) * Xs := by
    have hsum : Real.exp q + Real.exp (-q) = 2 * Real.cosh q := by
      rw [Real.cosh_eq]; ring
    have hmul : Real.exp q * Real.exp (-q) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    dsimp only [A, B, G, generator]
    have hprod : (1 - const (Real.exp q) * Xs) * (1 - const (Real.exp (-q)) * Xs) =
        1 - const (2 * Real.cosh q) * Xs + Xs ^ 2 := by
      rw [← hsum]
      simp only [map_add]
      have hm : const (Real.exp q) * const (Real.exp (-q)) = 1 := by
        rw [← map_mul, hmul, map_one]
      calc
        _ = 1 - (const (Real.exp q) + const (Real.exp (-q))) * Xs +
          (const (Real.exp q) * const (Real.exp (-q))) * Xs ^ 2 := by ring
        _ = _ := by rw [hm, one_mul]
    rw [hprod]
    simp only [mul_sub, map_sub, map_mul, map_one, map_ofNat]
    ring
  have h2 : H q 2 = Real.sinh q * (2 * (Real.cosh q - 1)) := by
    rw [H, Real.sinh_two_mul]; ring
  have hl : P * L = const (H q 2) := by
    apply PowerSeries.X_pow_mul_cancel (k := 2)
    calc
      Xs ^ 2 * (P * L) = P * (T - const (Real.sinh q) * N) := by rw [← hH]; ring
      _ = G ^ 2 * (A * B * T) - const (Real.sinh q) * (A * B) * (G ^ 2 * N) := by
        dsimp only [P]; ring
      _ = const (Real.sinh q) * Xs * (G ^ 2 - A * B) := by rw [hG, hS]; ring
      _ = Xs ^ 2 * const (H q 2) := by rw [hdif, h2]; simp only [map_mul]; ring
  have hh : P * (const (H q 2) * series (hom (Real.exp q) 1 1 (Real.exp (-q)))) =
      const (H q 2) := by
    have hf : P * series (hom (Real.exp q) 1 1 (Real.exp (-q))) = 1 := by
      calc
        _ = B * (G * (G * (A * series (hom (Real.exp q) 1 1 (Real.exp (-q)))))) := by
          dsimp only [P]; ring
        _ = _ := by
          change generator (Real.exp (-q)) * (generator 1 * (generator 1 *
            (generator (Real.exp q) * series (adjoin _ (adjoin _ (adjoin _ _)))))) = 1
          rw [adjoin_series, adjoin_series, adjoin_series, generator_geom]
    rw [mul_left_comm, hf, mul_one]
  have h := hl.trans hh.symm
  dsimp only [P] at h
  rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc] at h
  have he := generator_cancel _ (generator_cancel _ (generator_cancel _ (generator_cancel _ h)))
  simpa only [L, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul] using congrArg (coeff m) he

private lemma adjoin_two_geom (x y : ℝ) :
    adjoin x (fun j => y ^ j) = adjoin y (fun j => x ^ j) := by
  have h₁ : generator x * generator y * series (adjoin x (fun j => y ^ j)) = 1 := by
    rw [mul_comm (generator x), mul_assoc, adjoin_series, generator_geom]
  have h₂ : generator x * generator y * series (adjoin y (fun j => x ^ j)) = 1 := by
    rw [mul_assoc, adjoin_series, generator_geom]
  have h := h₁.trans h₂.symm
  rw [mul_assoc, mul_assoc] at h
  have h' := generator_cancel y (generator_cancel x h)
  funext m
  simpa only [PowerSeries.coeff_mk] using congrArg (coeff m) h'

private lemma hom_exp_reverse (q : ℝ) :
    hom (Real.exp q) 1 1 (Real.exp (-q)) = hom (Real.exp (-q)) 1 1 (Real.exp q) := by
  unfold hom
  rw [adjoin_swap (Real.exp q) 1, adjoin_swap (Real.exp q) 1, adjoin_two_geom,
    adjoin_swap 1 (Real.exp (-q)), adjoin_swap 1 (Real.exp (-q))]

private lemma scaled_ratio_mono (m : ℕ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    hom (u * u) u u 1 (m + 2) / hom (u * u) u u 1 m ≤
      hom (v * v) v v 1 (m + 2) / hom (v * v) v v 1 m := by
  have hv := hu.trans huv
  have h₁ := hom_first_ratio (mul_nonneg hu hu) (mul_le_mul huv huv hu hv)
    hu hu zero_lt_one m
  have h₂ := hom_first_ratio hu huv (mul_nonneg hv hv) hu zero_lt_one m
  have h₃ := hom_first_ratio hu huv (mul_nonneg hv hv) hv zero_lt_one m
  simp only [hom] at h₁ h₂ h₃ ⊢
  rw [adjoin_swap u (v * v), adjoin_swap v (v * v)] at h₂
  rw [adjoin_swap u (v * v), adjoin_swap u v] at h₃
  rw [adjoin_swap v (v * v)] at h₃
  exact h₁.trans (h₂.trans h₃)

private def radiusRatio (n : ℕ) (q : ℝ) : ℝ :=
  Real.log (H q (n + 1) / H q (n - 1)) / 2

private lemma exp_ratio (n : ℕ) (hn : 3 ≤ n) {q : ℝ} (hq : 0 < q) :
    Real.exp (2 * radiusRatio n q) = H q (n + 1) / H q (n - 1) := by
  unfold radiusRatio
  rw [show ∀ x : ℝ, 2 * (x / 2) = x by intro; ring, Real.exp_log]
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_pos (H_pos hq (by linarith)) (H_pos hq (by linarith))

private lemma normalized_ratio (m : ℕ) {q : ℝ} (hq : 0 < q) :
    Real.exp (2 * (radiusRatio (m + 3) q - q)) =
      hom (Real.exp (-q) * Real.exp (-q)) (Real.exp (-q)) (Real.exp (-q)) 1 (m + 2) /
      hom (Real.exp (-q) * Real.exp (-q)) (Real.exp (-q)) (Real.exp (-q)) 1 m := by
  let u := Real.exp (-q)
  have hprod : u * Real.exp q = 1 := by
    dsimp only [u]
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have he (k : ℕ) :
      hom (u * u) u u 1 k = u ^ k * hom (Real.exp q) 1 1 u k := by
    have h := hom_scale u (Real.exp (-q)) 1 1 (Real.exp q) k
    simpa only [hprod, mul_one, hom_exp_reverse, u] using h
  have h2 : H q 2 ≠ 0 := (H_pos hq (by norm_num)).ne'
  have hu : 0 < u := Real.exp_pos _
  have hden : hom (Real.exp q) 1 1 u m ≠ 0 :=
    (hom_pos (Real.exp_pos q).le zero_le_one zero_le_one hu m).ne'
  have hExp : Real.exp (-(2 * q)) = u ^ 2 := by
    dsimp [u]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [show 2 * (radiusRatio (m + 3) q - q) = 2 * radiusRatio (m + 3) q + -(2 * q) by ring,
    Real.exp_add, exp_ratio _ (by omega) hq, hExp]
  have hp : ((m + 3 : ℕ) : ℝ) + 1 = ((m + 2 : ℕ) : ℝ) + 2 := by
    push_cast
    ring
  have hm : ((m + 3 : ℕ) : ℝ) - 1 = (m : ℝ) + 2 := by
    push_cast
    ring
  rw [hp, hm, H_hom q (m + 2), H_hom q m]
  change (H q 2 * hom (Real.exp q) 1 1 u (m + 2)) /
    (H q 2 * hom (Real.exp q) 1 1 u m) * u ^ 2 =
      hom (u * u) u u 1 (m + 2) / hom (u * u) u u 1 m
  rw [he, he, pow_add]
  field_simp [h2, hden, hu.ne']

private lemma normalized_ratio_bounds (n : ℕ) (hn : 3 ≤ n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    a ≤ radiusRatio n a ∧ radiusRatio n b - b ≤ radiusRatio n a - a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hb := ha.trans_le hab
  have hzero (k : ℕ) : hom 0 0 0 1 k = 1 := by
    have hz (f : ℕ → ℝ) : adjoin 0 f = f := by
      funext k
      cases k <;> simp [adjoin]
    simp [hom, hz]
  constructor
  · have h := scaled_ratio_mono m (u := 0) le_rfl (Real.exp_pos (-a)).le
    rw [zero_mul, hzero, hzero, div_one, ← normalized_ratio m ha] at h
    have h' := Real.exp_le_exp.mp (show Real.exp 0 ≤ _ by simpa only [Real.exp_zero] using h)
    linarith
  · have h := scaled_ratio_mono m (Real.exp_pos (-b)).le
      (Real.exp_monotone (neg_le_neg hab))
    rw [← normalized_ratio m ha, ← normalized_ratio m hb] at h
    have h' := Real.exp_le_exp.mp h
    linarith

private lemma sinh_mid_sq (x y : ℝ) :
    Real.sinh ((x + y) / 2) ^ 2 = Real.sinh x * Real.sinh y + Real.sinh ((x - y) / 2) ^ 2 := by
  have h (u : ℝ) : Real.sinh (u / 2) ^ 2 = (Real.cosh u - 1) / 2 := by
    have h' := Real.cosh_two_mul (u / 2)
    rw [show 2 * (u / 2) = u by ring, Real.cosh_sq] at h'
    linarith
  rw [h, h, Real.cosh_add, Real.cosh_sub]
  ring

private lemma cosh_sub_eq (x y : ℝ) :
    Real.cosh x - Real.cosh y =
      2 * Real.sinh ((x + y) / 2) * Real.sinh ((x - y) / 2) := by
  let u := (x + y) / 2
  let v := (x - y) / 2
  have h₁ : u + v = x := by dsimp [u, v]; ring
  have h₂ : u - v = y := by dsimp [u, v]; ring
  have eq₁ := Real.cosh_add (x := u) (y := v)
  have eq₂ := Real.cosh_sub (x := u) (y := v)
  rw [h₁] at eq₁
  rw [h₂] at eq₂
  change _ = 2 * Real.sinh u * Real.sinh v
  linarith only [eq₁, eq₂]

private lemma coth_mul_mono : MonotoneOn (fun q : ℝ => q * Real.cosh q / Real.sinh q) (Set.Ioi 0) := by
  have hd (q : ℝ) (hq : 0 < q) : HasDerivAt (fun x : ℝ => x * Real.cosh x / Real.sinh x)
      ((Real.cosh q * Real.sinh q - q) / Real.sinh q ^ 2) q := by
    have h := ((hasDerivAt_id q).mul (Real.hasDerivAt_cosh q)).div (Real.hasDerivAt_sinh q)
      (Real.sinh_pos_iff.mpr hq).ne'
    convert h using 1
    · rfl
    · simp only [id_eq, Pi.mul_apply, one_mul]
      congr 1
      linear_combination q * Real.cosh_sq_sub_sinh_sq q
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hd x (by simpa using hx)).differentiableAt.differentiableWithinAt
  · intro q hq
    have hq' : 0 < q := by simpa using hq
    rw [(hd q hq').deriv]
    apply div_nonneg _ (sq_nonneg _)
    have h := mul_le_mul_of_nonneg_right (Real.one_le_cosh q) (Real.sinh_nonneg_iff.mpr hq'.le)
    linarith only [h, Real.self_le_sinh_iff.mpr hq'.le]

private lemma sinh_ratio_mono {s t : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    MonotoneOn (fun x : ℝ => Real.sinh (s * x) / Real.sinh (t * x)) (Set.Ioi 0) := by
  have hd (q : ℝ) (hq : 0 < q) :
      HasDerivAt (fun x => Real.sinh (s * x) / Real.sinh (t * x))
        ((Real.cosh (s * q) * s * Real.sinh (t * q) -
          Real.sinh (s * q) * (Real.cosh (t * q) * t)) / Real.sinh (t * q) ^ 2) q := by
    convert (((hasDerivAt_id q).const_mul s).sinh).div
      (((hasDerivAt_id q).const_mul t).sinh) (Real.sinh_pos_iff.mpr (mul_pos ht hq)).ne' using 1
    · rfl
    · simp only [id_eq, mul_one]
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hd x (by simpa using hx)).differentiableAt.differentiableWithinAt
  · intro q hq
    have hq' : 0 < q := by simpa using hq
    have h₁ := mul_pos ht hq'
    have h₂ := mul_pos (ht.trans_le hts) hq'
    have h := coth_mul_mono (show t * q ∈ Set.Ioi 0 from h₁)
      (show s * q ∈ Set.Ioi 0 from h₂) (mul_le_mul_of_nonneg_right hts hq'.le)
    rw [div_le_div_iff₀ (Real.sinh_pos_iff.mpr h₁) (Real.sinh_pos_iff.mpr h₂)] at h
    rw [(hd q hq').deriv]
    apply div_nonneg _ (sq_nonneg _)
    apply nonneg_of_mul_nonneg_right ?_ hq'
    linarith only [h]

private def Hq (s q : ℝ) : ℝ := s * (Real.cosh (s * q) - Real.cosh q)

private lemma Hq_pos {s q : ℝ} (hs : 1 < s) (hq : 0 < q) : 0 < Hq s q := by
  unfold Hq
  apply mul_pos (by linarith)
  rw [sub_pos, Real.cosh_lt_cosh, abs_of_pos hq, abs_of_pos (by positivity)]
  nlinarith

private lemma Hq_ratio_mono {s t : ℝ} (ht : 1 < t) (hts : t ≤ s) :
    MonotoneOn (fun q : ℝ => Hq s q / Hq t q) (Set.Ioi 0) := by
  have eq (q : ℝ) (hq : 0 < q) :
      Hq s q / Hq t q = (s / t) *
        (Real.sinh (((s + 1) / 2) * q) / Real.sinh (((t + 1) / 2) * q)) *
        (Real.sinh (((s - 1) / 2) * q) / Real.sinh (((t - 1) / 2) * q)) := by
    unfold Hq
    rw [cosh_sub_eq, cosh_sub_eq]
    have h₁ (u : ℝ) : (u * q + q) / 2 = (u + 1) / 2 * q := by ring
    have h₂ (u : ℝ) : (u * q - q) / 2 = (u - 1) / 2 * q := by ring
    rw [h₁, h₁, h₂, h₂]
    field_simp [(show t ≠ 0 by linarith), (Real.sinh_pos_iff.mpr (show 0 < (t + 1) / 2 * q by positivity)).ne',
      (Real.sinh_pos_iff.mpr (show 0 < (t - 1) / 2 * q by
        exact mul_pos (by linarith) hq)).ne']
  intro a ha b hb hab
  change Hq s a / Hq t a ≤ Hq s b / Hq t b
  rw [eq a ha, eq b hb]
  have ht₁ : 0 < (t + 1) / 2 := by linarith
  have ht₂ : 0 < (t - 1) / 2 := by linarith
  have hs₁ : 0 < (s + 1) / 2 := by linarith
  have hs₂ : 0 < (s - 1) / 2 := by linarith
  have h₁ := sinh_ratio_mono ht₁ (by linarith : (t + 1) / 2 ≤ (s + 1) / 2) ha hb hab
  have h₂ := sinh_ratio_mono ht₂ (by linarith : (t - 1) / 2 ≤ (s - 1) / 2) ha hb hab
  have hdiv : 0 ≤ s / t := div_nonneg (by linarith) (by linarith)
  exact mul_le_mul (mul_le_mul_of_nonneg_left h₁ hdiv) h₂
    (div_nonneg ((Real.sinh_pos_iff.mpr (mul_pos hs₂ ha)).le)
      ((Real.sinh_pos_iff.mpr (mul_pos ht₂ ha)).le))
    (mul_nonneg hdiv (div_nonneg ((Real.sinh_pos_iff.mpr (mul_pos hs₁ hb)).le)
      ((Real.sinh_pos_iff.mpr (mul_pos ht₁ hb)).le)))

private lemma H_ratio_mono {s t : ℝ} (ht : 1 < t) (hts : t ≤ s) :
    MonotoneOn (fun q : ℝ => H q s / H q t) (Set.Ioi 0) := by
  have hs : 1 < s := ht.trans_le hts
  have hder (q : ℝ) (hq : 0 < q) :
      HasDerivAt (fun x => H x s / H x t)
        ((Hq s q * H q t - H q s * Hq t q) / H q t ^ 2) q :=
    (H_deriv_q s q).div (H_deriv_q t q) (H_pos hq ht).ne'
  have hcont (s : ℝ) : Continuous (fun x => H x s) :=
    continuous_iff_continuousAt.mpr (fun x => (H_deriv_q s x).continuousAt)
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun q hq => (hder q hq).continuousAt.continuousWithinAt
  · exact fun q hq => (hder q (by simpa using hq)).differentiableAt.differentiableWithinAt
  · intro q hq
    have hq' : 0 < q := by simpa using hq
    obtain ⟨p, hp, hp'⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
      (fun x => H x s) (Hq s) hq' (hcont s).continuousOn
      (fun x _ => H_deriv_q s x)
      (fun x => H x t) (Hq t) (hcont t).continuousOn
      (fun x _ => H_deriv_q t x)
    have hratio := Hq_ratio_mono ht hts (show p ∈ Set.Ioi 0 from hp.1)
      (show q ∈ Set.Ioi 0 from hq') hp.2.le
    rw [div_le_div_iff₀ (Hq_pos ht hp.1) (Hq_pos ht hq')] at hratio
    have hc : H q t * Hq s p = H q s * Hq t p := by simpa [H] using hp'
    rw [(hder q hq').deriv]
    apply div_nonneg _ (sq_nonneg _)
    change 0 ≤ Hq s q * H q t - H q s * Hq t q
    apply nonneg_of_mul_nonneg_right ?_ (Hq_pos ht hp.1)
    have hmul := mul_le_mul_of_nonneg_right hratio (H_pos hq' ht).le
    have hre := congrArg (· * Hq t q) hc
    linarith only [hmul, hre]

private lemma radiusRatio_mono (n : ℕ) (hn : 3 ≤ n) :
    MonotoneOn (radiusRatio n) (Set.Ioi 0) := by
  intro a ha b hb hab
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h₁ : (1 : ℝ) < (n : ℝ) - 1 := by linarith
  have h₂ : (n : ℝ) - 1 ≤ (n : ℝ) + 1 := by linarith
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
  exact Real.log_le_log (div_pos (H_pos ha (by linarith)) (H_pos ha h₁))
    (H_ratio_mono h₁ h₂ ha hb hab)

private lemma H_difference (q s : ℝ) :
    H q (s + 1) - H q (s - 1) = 2 * Real.sinh q * (Real.cosh (s * q) - 1) := by
  unfold H
  rw [add_mul, sub_mul, one_mul, Real.sinh_add, Real.sinh_sub]
  ring

private lemma sinh_comparison {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hau : a ≤ u) (hbv : b ≤ v) (hd : |u - v| ≤ |a - b|) :
    Real.sinh ((u + v) / 2) ^ 2 * (Real.sinh a * Real.sinh b) ≤
      Real.sinh ((a + b) / 2) ^ 2 * (Real.sinh u * Real.sinh v) := by
  have hs : Real.sinh a * Real.sinh b ≤ Real.sinh u * Real.sinh v :=
    mul_le_mul (Real.sinh_le_sinh.mpr hau) (Real.sinh_le_sinh.mpr hbv)
      (Real.sinh_nonneg_iff.mpr hb.le) (Real.sinh_nonneg_iff.mpr (ha.le.trans hau))
  have hsd : Real.sinh ((u - v) / 2) ^ 2 ≤ Real.sinh ((a - b) / 2) ^ 2 := by
    rw [← sq_abs (Real.sinh ((u - v) / 2)), ← sq_abs (Real.sinh ((a - b) / 2))]
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2
    rw [Real.abs_sinh, Real.abs_sinh, Real.sinh_le_sinh, abs_div, abs_div]
    exact div_le_div_of_nonneg_right hd (abs_nonneg _)
  rw [sinh_mid_sq, sinh_mid_sq]
  have h := mul_le_mul hsd hs
    (mul_nonneg (Real.sinh_nonneg_iff.mpr ha.le) (Real.sinh_nonneg_iff.mpr hb.le)) (sq_nonneg _)
  linarith only [h]

private lemma endpoint_remainder_ordered (n : ℕ) (hn : 3 ≤ n) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    (radii a b (n + 1) - radii a b (n - 1)) / 2 ≤ meanTerm n a b * radii a b n := by
  have hb := ha.trans_le hab
  let r := radiusRatio n
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hminus : (1 : ℝ) < (n : ℝ) - 1 := by linarith
  have hplus : (1 : ℝ) < (n : ℝ) + 1 := by linarith
  let p (q : ℝ) := H q ((n : ℝ) + 1)
  let m (q : ℝ) := H q ((n : ℝ) - 1)
  let T (q : ℝ) := Real.sqrt (p q * m q)
  have hp {q : ℝ} (hq : 0 < q) : 0 < p q := H_pos hq hplus
  have hm {q : ℝ} (hq : 0 < q) : 0 < m q := H_pos hq hminus
  have hT {q : ℝ} (hq : 0 < q) : 0 ≤ T q := Real.sqrt_nonneg _
  have T_sq {q : ℝ} (hq : 0 < q) : T q ^ 2 = p q * m q :=
    Real.sq_sqrt (mul_nonneg (hp hq).le (hm hq).le)
  have plus_form {q : ℝ} (hq : 0 < q) : p q = T q * Real.exp (r q) := by
    apply (sq_eq_sq₀ (hp hq).le (mul_nonneg (hT hq) (Real.exp_pos _).le)).1
    rw [mul_pow, T_sq hq, ← Real.exp_nat_mul, Nat.cast_ofNat, exp_ratio n hn hq]
    change p q ^ 2 = p q * m q * (p q / m q)
    field_simp [(hm hq).ne']
  have minus_form {q : ℝ} (hq : 0 < q) : m q = T q * Real.exp (-(r q)) := by
    apply (sq_eq_sq₀ (hm hq).le (mul_nonneg (hT hq) (Real.exp_pos _).le)).1
    rw [mul_pow, T_sq hq, ← Real.exp_nat_mul, Nat.cast_ofNat, mul_neg,
      Real.exp_neg, exp_ratio n hn hq]
    change m q ^ 2 = p q * m q * (p q / m q)⁻¹
    field_simp [(hm hq).ne', (hp hq).ne']
  let U := radii a b
  let K := Real.sqrt (T a * T b)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hKsq : K ^ 2 = T a * T b := Real.sq_sqrt (mul_nonneg (hT ha) (hT hb))
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := Nat.cast_sub (by omega)
  have hUp : U (n + 1) = K * Real.exp ((r a + r b) / 2) := by
    apply (sq_eq_sq₀ (radii_nonneg _ _ (by omega)) (mul_nonneg hK (Real.exp_pos _).le)).1
    rw [show U (n + 1) ^ 2 = H a (n + 1 : ℕ) * H b (n + 1 : ℕ) from
        radii_sq a b ha hb (by omega),
      Nat.cast_add_one, mul_pow, hKsq, ← Real.exp_nat_mul, Nat.cast_ofNat,
      show 2 * ((r a + r b) / 2) = r a + r b by ring, Real.exp_add]
    change p a * p b = _
    rw [plus_form ha, plus_form hb]
    ring
  have hUm : U (n - 1) = K * Real.exp (-((r a + r b) / 2)) := by
    apply (sq_eq_sq₀ (radii_nonneg _ _ (by omega)) (mul_nonneg hK (Real.exp_pos _).le)).1
    rw [show U (n - 1) ^ 2 = H a (n - 1 : ℕ) * H b (n - 1 : ℕ) from
        radii_sq a b ha hb (by omega),
      hcast, mul_pow, hKsq, ← Real.exp_nat_mul, Nat.cast_ofNat,
      show 2 * (-((r a + r b) / 2)) = -r a + -r b by ring, Real.exp_add]
    change m a * m b = _
    rw [minus_form ha, minus_form hb]
    ring
  have hf {q : ℝ} (hq : 0 < q) :
    T q * Real.sinh (r q) = Real.sinh q * (Real.cosh (n * q) - 1) := by
    calc
      _ = (p q - m q) / 2 := by rw [Real.sinh_eq, plus_form hq, minus_form hq]; ring
      _ = _ := by dsimp only [p, m]; rw [H_difference]; ring
  have hu := (normalized_ratio_bounds n hn ha hab).1
  have hv := (normalized_ratio_bounds n hn hb le_rfl).1
  have hr := radiusRatio_mono n hn (show a ∈ Set.Ioi 0 from ha)
    (show b ∈ Set.Ioi 0 from hb) hab
  have hd : |r a - r b| ≤ |a - b| := by
    rw [abs_of_nonpos (sub_nonpos.mpr hr), abs_of_nonpos (sub_nonpos.mpr hab)]
    have h := (normalized_ratio_bounds n hn ha hab).2
    dsimp only [r] at *
    linarith only [h]
  have hcmp := sinh_comparison ha hb hu hv hd
  have hSA := Real.sinh_pos_iff.mpr ha
  have hSB := Real.sinh_pos_iff.mpr hb
  have hC := Real.sinh_pos_iff.mpr (show 0 < midpoint a b by unfold midpoint; linarith)
  have hmid := Real.sinh_nonneg_iff.mpr (show 0 ≤ (r a + r b) / 2 by linarith)
  have hW {q : ℝ} (hq : 0 < q) : 0 ≤ logWeight n q :=
    div_nonneg (sub_nonneg.mpr (Real.one_le_cosh _)) (H_pos hq (by linarith)).le
  rw [show (radii a b (n + 1) - radii a b (n - 1)) / 2 =
    K * Real.sinh ((r a + r b) / 2) by
      change (U (n + 1) - U (n - 1)) / 2 = _
      rw [hUp, hUm, Real.sinh_eq]; ring]
  apply (sq_le_sq₀ (mul_nonneg hK hmid)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC.le) (radii_nonneg _ _ (by omega)))).1
  rw [mul_pow, hKsq]
  simp only [mul_pow, Real.sq_sqrt (mul_nonneg (hW ha) (hW hb)),
    radii_sq a b ha hb (m := n) (by omega : 2 ≤ n)]
  apply le_of_mul_le_mul_right ?_ (mul_pos hSA hSB)
  have hmul := mul_le_mul_of_nonneg_left hcmp (mul_nonneg (hT ha) (hT hb))
  have hw {q : ℝ} (hq : 0 < q) : logWeight n q * H q n = Real.cosh (n * q) - 1 := by
    unfold logWeight
    exact div_mul_cancel₀ _ (H_pos hq (by linarith)).ne'
  change _ ≤ _ at hmul
  calc
    _ = (T a * T b) * (Real.sinh ((r a + r b) / 2) ^ 2 * (Real.sinh a * Real.sinh b)) := by ring
    _ ≤ (T a * T b) * (Real.sinh (midpoint a b) ^ 2 * (Real.sinh (r a) * Real.sinh (r b))) := hmul
    _ = Real.sinh (midpoint a b) ^ 2 * ((T a * Real.sinh (r a)) * (T b * Real.sinh (r b))) := by ring
    _ = _ := by rw [hf ha, hf hb, ← hw ha, ← hw hb]; ring

/-- Lemmas 4.1–4.2. The geometric mean gives E_n ≥ 0, and the first three
Fejér weights have the explicit nonnegative bounds in the paper. -/
theorem hyperbolic_endpoint_bounds (n : ℕ) (hn : 3 ≤ n) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ meanTerm n a b * radii a b n - (radii a b (n + 1) - radii a b (n - 1)) / 2 ∧
      ∀ j < 3, 0 ≤ fejerWeight (radii a b) (Real.cosh (midpoint a b)) j := by
  refine ⟨sub_nonneg.mpr ?_, first_weights a b ha hb⟩
  rcases le_total a b with hab | hab
  · exact endpoint_remainder_ordered n hn a b ha hab
  · have hu (k : ℕ) : radii a b k = radii b a k := by simp [radii, radialU, mul_comm]
    have hm : meanTerm n a b = meanTerm n b a := by simp [meanTerm, midpoint, mul_comm, add_comm]
    simpa only [← hu, ← hm] using endpoint_remainder_ordered n hn b a hb hab

/-! ## Green kernels -/

private lemma H_analytic (q s : ℝ) : AnalyticAt ℝ (H q) s := by
  unfold H
  exact (Real.analyticAt_sinh.comp (analyticAt_id.mul analyticAt_const)).sub
    (analyticAt_id.mul analyticAt_const)

/-- Factor out s−1 before taking the square root. The divided difference is
analytic at 1 and its value there is q cosh q − sinh q. -/
private lemma radialU_smooth (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) (hs : 1 ≤ s) :
    ContDiffAt ℝ ∞ (radialU a b) s := by
  by_cases h : s = 1
  · subst s
    let F (q : ℝ) := dslope (H q) 1
    have hF (q : ℝ) : AnalyticAt ℝ (F q) 1 := (H_analytic q 1).dslope 1
    have hp {q : ℝ} (hq : 0 < q) : 0 < F q 1 := by
      simpa only [F, dslope_same, (H_deriv_s q 1).deriv, one_mul] using sinh_mul_sub_pos hq
    have hp' : 0 < F a 1 * F b 1 := mul_pos (hp ha) (hp hb)
    have hP : ContDiffAt ℝ ∞ (fun x => F a x * F b x) 1 := ((hF a).mul (hF b)).contDiffAt
    have hG : ContDiffAt ℝ ∞ (fun x => (x - 1) * Real.sqrt (F a x * F b x)) 1 :=
      (contDiffAt_id.sub contDiffAt_const).mul (hP.sqrt hp'.ne')
    apply hG.congr_of_eventuallyEq
    filter_upwards with x
    have hfactor (q : ℝ) : H q x = (x - 1) * F q x := by
      simpa [F, H, smul_eq_mul] using (sub_smul_dslope (H q) 1 x).symm
    rw [radialU, hfactor a, hfactor b,
      show (x - 1) * F a x * ((x - 1) * F b x) = (x - 1) ^ 2 * (F a x * F b x) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    by_cases hx' : x < 1
    · rw [ite_eq_left hx', abs_of_neg (sub_neg.mpr hx')]
      ring
    · rw [ite_eq_right hx', abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hx'))]
  · have hs' : 1 < s := lt_of_le_of_ne hs (Ne.symm h)
    apply (((H_analytic a s).mul (H_analytic b s)).contDiffAt.sqrt
      (mul_pos (H_pos ha hs') (H_pos hb hs')).ne').congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hs'] with x hx
    simp [radialU, not_lt.mpr hx.le]

private lemma smooth_iterated {F : ℝ → ℝ} {x : ℝ} (h : ContDiffAt ℝ ∞ F x) :
    ∀ k : ℕ, ContDiffAt ℝ ∞ (iteratedDeriv k F) x := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.derivWithin (by simp)

private lemma hasDeriv_iterated {F : ℝ → ℝ} {x : ℝ} (h : ContDiffAt ℝ ∞ F x) (k : ℕ) :
    HasDerivAt (iteratedDeriv k F) (iteratedDeriv (k + 1) F x) x := by
  rw [iteratedDeriv_succ]
  exact ((smooth_iterated h k).differentiableAt (by simp)).hasDerivAt

private def greenValue (h u : ℝ) : ℝ := if h = 0 then u else Real.sinh (h * u) / h

private lemma greenValue_deriv (h u : ℝ) :
    HasDerivAt (greenValue h) (Real.cosh (h * u)) u := by
  by_cases hh : h = 0
  · subst h
    have he : greenValue 0 = id := by funext x; simp [greenValue]
    simpa only [he, zero_mul, Real.cosh_zero] using hasDerivAt_id u
  · have hd := (((hasDerivAt_id u).const_mul h).sinh).div_const h
    have he : greenValue h = fun x => Real.sinh (h * x) / h := by
      funext x; simp [greenValue, hh]
    simpa [he, hh, id, mul_div_cancel_right₀] using hd

/-- Integration by parts on each half of the interval for the Green kernel of
the centered hyperbolic difference. This also covers the triangular kernel
at h = 0. -/
private lemma centered_integral (h s : ℝ) {F F₁ F₂ : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc (s - 1) (s + 1), HasDerivAt F (F₁ x) x)
    (hF₁ : ∀ x ∈ Set.Icc (s - 1) (s + 1), HasDerivAt F₁ (F₂ x) x)
    (hF₂ : ContinuousOn F₂ (Set.Icc (s - 1) (s + 1))) :
    (∫ u in (-1 : ℝ)..1, greenValue h (1 - |u|) * (F₂ (s + u) - h ^ 2 * F (s + u))) =
      F (s + 1) + F (s - 1) - 2 * Real.cosh h * F s := by
  let integrand (u : ℝ) := greenValue h (1 - |u|) * (F₂ (s + u) - h ^ 2 * F (s + u))
  have hFcont : ContinuousOn F (Set.Icc (s - 1) (s + 1)) :=
    fun x hx => (hF x hx).continuousAt.continuousWithinAt
  have int_cont (l r : ℝ) (hl : -1 ≤ l) (hr : r ≤ 1) (hlr : l ≤ r) :
      ContinuousOn integrand (Set.uIcc l r) := by
    have hsmap : Set.MapsTo (fun u => s + u) (Set.uIcc l r) (Set.Icc (s - 1) (s + 1)) := by
      intro u hu
      rw [Set.uIcc_of_le hlr] at hu
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hk : Continuous (greenValue h) := continuous_iff_continuousAt.2
      (fun u => (greenValue_deriv h u).continuousAt)
    exact (hk.comp (continuous_const.sub continuous_abs)).continuousOn.mul
      ((hF₂.comp (by fun_prop) hsmap).sub
        (continuousOn_const.mul (hFcont.comp (by fun_prop) hsmap)))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((int_cont (-1) 0 (by norm_num) (by norm_num) (by norm_num)).intervalIntegrable
      (μ := MeasureTheory.MeasureSpace.volume))
    ((int_cont 0 1 (by norm_num) le_rfl (by norm_num)).intervalIntegrable
      (μ := MeasureTheory.MeasureSpace.volume))
  have primitive (ε l r : ℝ) (he : ε ^ 2 = 1)
      (hlr : l ≤ r) (hl : -1 ≤ l) (hr : r ≤ 1)
      (habs : ∀ u ∈ Set.uIcc l r, 1 - |u| = 1 + ε * u) :
      (∫ u in l..r, integrand u) =
        (greenValue h (1 + ε * r) * F₁ (s + r) -
          ε * Real.cosh (h * (1 + ε * r)) * F (s + r)) -
        (greenValue h (1 + ε * l) * F₁ (s + l) -
          ε * Real.cosh (h * (1 + ε * l)) * F (s + l)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (int_cont l r hl hr hlr).intervalIntegrable
    intro u hu
    have hu' : u ∈ Set.Icc l r := Set.uIcc_of_le hlr ▸ hu
    have hsu : s + u ∈ Set.Icc (s - 1) (s + 1) :=
      ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
    have hs' : HasDerivAt (fun x => s + x) 1 u := by simpa using (hasDerivAt_id u).const_add s
    have huDer : HasDerivAt (fun x => 1 + ε * x) ε u := by
      simpa using ((hasDerivAt_id u).const_mul ε).const_add 1
    have hk := (greenValue_deriv h (1 + ε * u)).comp u huDer
    have hc := ((huDer.const_mul h).cosh).const_mul ε
    have hf := (hF (s + u) hsu).comp u hs'
    have hf₁ := (hF₁ (s + u) hsu).comp u hs'
    have hk₂ (v : ℝ) : h * Real.sinh (h * v) = h ^ 2 * greenValue h v := by
      by_cases hh : h = 0
      · simp [hh]
      · simp only [greenValue, ite_eq_right hh]
        field_simp
    convert (hk.mul hf₁).sub (hc.mul hf) using 1
    · rfl
    · simp only [integrand, habs u hu, Function.comp_apply, mul_one]
      linear_combination F (s + u) * (hk₂ (1 + ε * u)) +
        (h * Real.sinh (h * (1 + ε * u)) * F (s + u)) * he
  have left := primitive 1 (-1) 0 (by norm_num) (by norm_num) le_rfl (by norm_num)
    (fun u hu => by
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hu
      rw [abs_of_nonpos hu.2]; ring)
  have right := primitive (-1) 0 1 (by norm_num) (by norm_num) (by norm_num) le_rfl
    (fun u hu => by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      rw [abs_of_nonneg hu.1]; ring)
  have zero : greenValue h 0 = 0 := by simp [greenValue]
  change (∫ u in (-1 : ℝ)..1, integrand u) = _
  rw [← hsplit, left, right]
  norm_num [zero, sub_eq_add_neg]
  ring

set_option maxHeartbeats 1000000 in
/-- Lemma 4.3. Integration by parts for the triangular and hyperbolic Green kernels. -/
theorem green_kernel_identity (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (m : ℕ) (hm : 3 ≤ m) :
    2 * fejerWeight (radii a b) (Real.cosh (midpoint a b)) m =
      ∫ u in (-1 : ℝ)..1, triangular u *
        (∫ v in (-1 : ℝ)..1, green (midpoint a b) v * differential a b ((m : ℝ) + u + v)) := by
  let c := midpoint a b
  have hc : 0 < c := by unfold c midpoint; positivity
  let U := radialU a b
  let J (k : ℕ) (s : ℝ) :=
    iteratedDeriv k U (s + 1) + iteratedDeriv k U (s - 1) -
      2 * Real.cosh c * iteratedDeriv k U s
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have J_deriv (k : ℕ) (s : ℝ) (hs : 2 ≤ s) : HasDerivAt (J k) (J (k + 1) s) s := by
    have hp := (hasDeriv_iterated (radialU_smooth a b (s + 1) ha hb (by linarith)) k).comp s
      (show HasDerivAt (fun x : ℝ => x + 1) 1 s by simpa using (hasDerivAt_id s).add_const 1)
    have hq := (hasDeriv_iterated (radialU_smooth a b (s - 1) ha hb (by linarith)) k).comp s
      (show HasDerivAt (fun x : ℝ => x - 1) 1 s by simpa using (hasDerivAt_id s).sub_const 1)
    have hs' := hasDeriv_iterated (radialU_smooth a b s ha hb (by linarith)) k
    convert (hp.add hq).sub (hs'.const_mul (2 * Real.cosh c)) using 1
    · rfl
    · simp only [J, U, mul_one]
  have hout := centered_integral 0 (m : ℝ) (F := J 0) (F₁ := J 1) (F₂ := J 2)
    (fun t ht => J_deriv 0 t (by linarith [ht.1]))
    (fun t ht => J_deriv 1 t (by linarith [ht.1]))
    (fun t ht => (J_deriv 2 t (by linarith [ht.1])).continuousAt.continuousWithinAt)
  have hin (s : ℝ) (hs : 2 ≤ s) :
      (∫ v in (-1 : ℝ)..1, green c v * differential a b (s + v)) = J 2 s := by
    have h := centered_integral c s (F := iteratedDeriv 2 U) (F₁ := iteratedDeriv 3 U)
      (F₂ := iteratedDeriv 4 U)
      (fun t ht => hasDeriv_iterated (radialU_smooth a b t ha hb (by linarith [ht.1])) 2)
      (fun t ht => hasDeriv_iterated (radialU_smooth a b t ha hb (by linarith [ht.1])) 3)
      (fun t ht => by
        have hc := smooth_iterated (radialU_smooth a b t ha hb (by linarith [ht.1])) 4
        exact hc.continuousAt.continuousWithinAt)
    simpa only [green, differential, greenValue, ite_eq_right hc.ne', c, J, U] using h
  have ha' (k : ℕ) (hk : 1 ≤ k) :
      2 * auxiliary (radii a b) (Real.cosh c) k = J 0 k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [auxiliary, J, iteratedDeriv_zero, radii, U, Nat.cast_add, Nat.cast_one]
    rw [show (j : ℝ) + 1 - 1 = j by ring]
    ring_nf
  have hweight : 2 * fejerWeight (radii a b) (Real.cosh c) m =
      J 0 (m + 1) + J 0 (m - 1) - 2 * Real.cosh 0 * J 0 m := by
    simp only [fejerWeight, mul_sub, mul_add]
    rw [ha' (m + 1) (by omega), ha' m (by omega), ha' (m - 1) (by omega),
      Nat.cast_add_one, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one, Real.cosh_zero]
    ring
  rw [hweight, ← hout]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
  dsimp only
  rw [hin ((m : ℝ) + u) (by linarith [hu.1])]
  simp [greenValue, triangular]

section DifferentialInequality

open Set MeasureTheory intervalIntegral
set_option maxHeartbeats 400000

/-! ### Algebra of the fourth derivative -/

private def h₁ (q s : ℝ) : ℝ := q * Real.cosh (s * q) - Real.sinh q
private def h₂ (q s : ℝ) : ℝ := q ^ 2 * Real.sinh (s * q)
private def h₃ (q s : ℝ) : ℝ := q ^ 3 * Real.cosh (s * q)

private def p (q s : ℝ) : ℝ := h₁ q s / H q s
private def A₂ (q s : ℝ) : ℝ := h₂ q s / H q s
private def A₃ (q s : ℝ) : ℝ := h₃ q s / H q s
private def w (q s : ℝ) : ℝ := A₂ q s - q * p q s
private def j (q s : ℝ) : ℝ := A₃ q s - q * A₂ q s

private lemma h₁_deriv (q s : ℝ) : HasDerivAt (h₁ q) (h₂ q s) s := by
  convert ((((hasDerivAt_id s).mul_const q).cosh).const_mul q).sub
    (hasDerivAt_const s (Real.sinh q)) using 1
  · rfl
  · simp only [id_eq, one_mul, sub_zero, h₂]
    ring

private lemma h₂_deriv (q s : ℝ) : HasDerivAt (h₂ q) (h₃ q s) s := by
  convert (((hasDerivAt_id s).mul_const q).sinh).const_mul (q ^ 2) using 1
  · rfl
  · simp only [id_eq, one_mul, h₃]
    ring

private lemma h₃_deriv (q s : ℝ) :
    HasDerivAt (h₃ q) (q ^ 2 * h₂ q s) s := by
  convert (((hasDerivAt_id s).mul_const q).cosh).const_mul (q ^ 3) using 1
  · rfl
  · simp only [id_eq, one_mul, h₂]
    ring

private lemma p_deriv {q s : ℝ} (hq : 0 < q) (hs : 1 < s) :
    HasDerivAt (p q) (A₂ q s - p q s ^ 2) s := by
  convert (h₁_deriv q s).div (H_deriv_s q s) (H_pos hq hs).ne' using 1
  · rfl
  · change _ = (h₂ q s * H q s - h₁ q s * h₁ q s) / H q s ^ 2
    unfold p A₂
    field_simp [(H_pos hq hs).ne']

private lemma A₂_deriv {q s : ℝ} (hq : 0 < q) (hs : 1 < s) :
    HasDerivAt (A₂ q) (A₃ q s - A₂ q s * p q s) s := by
  convert (h₂_deriv q s).div (H_deriv_s q s) (H_pos hq hs).ne' using 1
  · rfl
  · change _ = (h₃ q s * H q s - h₂ q s * h₁ q s) / H q s ^ 2
    unfold A₂ A₃ p
    field_simp [(H_pos hq hs).ne']

private lemma A₃_deriv {q s : ℝ} (hq : 0 < q) (hs : 1 < s) :
    HasDerivAt (A₃ q) (q ^ 2 * A₂ q s - A₃ q s * p q s) s := by
  convert (h₃_deriv q s).div (H_deriv_s q s) (H_pos hq hs).ne' using 1
  · rfl
  · change _ = (q ^ 2 * h₂ q s * H q s - h₃ q s * h₁ q s) / H q s ^ 2
    unfold A₂ A₃ p
    field_simp [(H_pos hq hs).ne']

private lemma radialU_pos {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 1 < s) :
    0 < radialU a b s := by
  rw [radialU, ite_eq_right hs.not_gt]
  exact Real.sqrt_pos.2 (mul_pos (H_pos ha hs) (H_pos hb hs))

private def avg (x y : ℝ) : ℝ := (x + y) / 2
private def halfDiff (x y : ℝ) : ℝ := (x - y) / 2

private lemma radialU_deriv {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 1 < s) :
    HasDerivAt (radialU a b) (avg (p a s) (p b s) * radialU a b s) s := by
  have hA := H_pos ha hs
  have hB := H_pos hb hs
  have he :
      radialU a b =ᶠ[𝓝 s] fun t => Real.sqrt (H a t * H b t) := by
    filter_upwards [lt_mem_nhds hs] with t ht
    simp [radialU, ht.not_gt]
  refine (( (H_deriv_s a s).mul (H_deriv_s b s)).sqrt
    (mul_pos hA hB).ne').congr_of_eventuallyEq he
    |>.congr_deriv ?_
  rw [radialU, ite_eq_right hs.not_gt]
  set z := Real.sqrt (H a s * H b s)
  have hz : 0 < z := Real.sqrt_pos.2 (mul_pos hA hB)
  have hz₂ : z ^ 2 = H a s * H b s := Real.sq_sqrt (mul_pos hA hB).le
  unfold avg p
  change (h₁ a s * H b s + H a s * h₁ b s) / (2 * z) =
    (h₁ a s / H a s + h₁ b s / H b s) / 2 * z
  field_simp [hA.ne', hB.ne', hz.ne']
  linear_combination -(h₁ a s * H b s + h₁ b s * H a s) * hz₂

private def p₁ (q s : ℝ) : ℝ := A₂ q s - p q s ^ 2
private def p₂ (q s : ℝ) : ℝ := A₃ q s - 3 * p q s * A₂ q s + 2 * p q s ^ 3
private def p₃ (q s : ℝ) : ℝ :=
  q ^ 2 * A₂ q s - 4 * p q s * A₃ q s - 3 * A₂ q s ^ 2 +
    12 * p q s ^ 2 * A₂ q s - 6 * p q s ^ 4

private lemma p₁_deriv {q s : ℝ} (hq : 0 < q) (hs : 1 < s) :
    HasDerivAt (p₁ q) (p₂ q s) s := by
  convert (A₂_deriv hq hs).sub ((p_deriv hq hs).pow 2) using 1
  · rfl
  · dsimp [p₂]
    ring

private lemma p₂_deriv {q s : ℝ} (hq : 0 < q) (hs : 1 < s) :
    HasDerivAt (p₂ q) (p₃ q s) s := by
  convert (((A₃_deriv hq hs).sub
    (((p_deriv hq hs).const_mul 3).mul (A₂_deriv hq hs))).add
    (((p_deriv hq hs).pow 3).const_mul 2)) using 1
  · rfl
  · dsimp [p₃]
    ring

private def P₀ (a b s : ℝ) : ℝ := avg (p a s) (p b s)
private def P₁ (a b s : ℝ) : ℝ := avg (p₁ a s) (p₁ b s)
private def P₂ (a b s : ℝ) : ℝ := avg (p₂ a s) (p₂ b s)
private def P₃ (a b s : ℝ) : ℝ := avg (p₃ a s) (p₃ b s)

private lemma eqOn_iterated_succ {F G : ℝ → ℝ} {k : ℕ} {s : ℝ}
    (hs : 1 < s) (hEq : Set.EqOn (iteratedDeriv k F) G (Set.Ioi (1 : ℝ)))
    {g : ℝ} (hG : HasDerivAt G g s) : iteratedDeriv (k + 1) F s = g := by
  rw [iteratedDeriv_succ]
  exact (hG.congr_of_eventuallyEq
    (by filter_upwards [lt_mem_nhds hs] with t ht using hEq ht)).deriv

private lemma radialU_jets {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ s > 1,
      iteratedDeriv 2 (radialU a b) s =
        (P₁ a b s + P₀ a b s ^ 2) * radialU a b s ∧
      iteratedDeriv 4 (radialU a b) s =
        (P₃ a b s + 4 * P₀ a b s * P₂ a b s + 3 * P₁ a b s ^ 2 +
         6 * P₀ a b s ^ 2 * P₁ a b s + P₀ a b s ^ 4) * radialU a b s := by
  let V := radialU a b
  let P := P₀ a b
  let X := P₁ a b
  let Y := P₂ a b
  let Z := P₃ a b
  have hV (s : ℝ) (hs : 1 < s) : HasDerivAt V (P s * V s) s := radialU_deriv ha hb hs
  have hP (s : ℝ) (hs : 1 < s) : HasDerivAt P (X s) s :=
    ((p_deriv ha hs).add (p_deriv hb hs)).div_const 2
  have hX (s : ℝ) (hs : 1 < s) : HasDerivAt X (Y s) s :=
    ((p₁_deriv ha hs).add (p₁_deriv hb hs)).div_const 2
  have hY (s : ℝ) (hs : 1 < s) : HasDerivAt Y (Z s) s :=
    ((p₂_deriv ha hs).add (p₂_deriv hb hs)).div_const 2
  have e1 : Set.EqOn (iteratedDeriv 1 V) (fun s => P s * V s) (Set.Ioi 1) :=
    fun s hs => by simpa only [iteratedDeriv_one] using (hV s hs).deriv
  have e2 : Set.EqOn (iteratedDeriv 2 V) (fun s => (X s + P s ^ 2) * V s) (Set.Ioi 1) := by
    intro s hs
    refine eqOn_iterated_succ hs e1 ?_
    convert (hP s hs).mul (hV s hs) using 1; ring
  have e3 : Set.EqOn (iteratedDeriv 3 V) (fun s => (Y s + 3 * P s * X s + P s ^ 3) * V s)
      (Set.Ioi 1) := by
    intro s hs
    refine eqOn_iterated_succ hs e2 ?_
    convert ((hX s hs).add ((hP s hs).pow 2)).mul (hV s hs) using 1; dsimp [Pi.add_apply, Pi.pow_apply]; ring
  intro s hs
  refine ⟨e2 hs, eqOn_iterated_succ hs e3 ?_⟩
  convert (((hY s hs).add (((hP s hs).const_mul 3).mul (hX s hs))).add
    ((hP s hs).pow 3)).mul (hV s hs) using 1
  dsimp [P, X, Y, Z, V, Pi.add_apply, Pi.pow_apply, Pi.mul_apply]
  ring

/-- The polynomial identity after substituting the derivative formulas for the
two logarithmic derivatives. Here A₂ = q p + w and A₃ = q A₂ + j. -/
private lemma fourth_factor_algebra (a b pa pb wa wb ja jb : ℝ) :
    let c := avg a b
    let d := halfDiff a b
    let P := avg pa pb
    let D := halfDiff pa pb
    let Aa := a * pa + wa
    let Ab := b * pb + wb
    let Ba := a * Aa + ja
    let Bb := b * Ab + jb
    let X := avg (Aa - pa ^ 2) (Ab - pb ^ 2)
    let Y := avg (Ba - 3 * pa * Aa + 2 * pa ^ 3) (Bb - 3 * pb * Ab + 2 * pb ^ 3)
    let T := avg (a ^ 2 * Aa - 4 * pa * Ba - 3 * Aa ^ 2 + 12 * pa ^ 2 * Aa - 6 * pa ^ 4)
      (b ^ 2 * Ab - 4 * pb * Bb - 3 * Ab ^ 2 + 12 * pb ^ 2 * Ab - 6 * pb ^ 4)
    let D' := halfDiff (Aa - pa ^ 2) (Ab - pb ^ 2)
    let S := P - c
    let Z := c * (d - D) - D'
    T + 4 * P * Y + 3 * X ^ 2 + 6 * P ^ 2 * X + P ^ 4 - c ^ 2 * (X + P ^ 2) =
      avg wa wb * ((d - 2 * D) ^ 2 + 2 * D ^ 2) - 4 * D * halfDiff ja jb +
      (d - D) * D * (d ^ 2 - 3 * d * D + 3 * D ^ 2) +
      Z * (c * (d + D) + 3 * D') + c * S * (d ^ 2 - 2 * D ^ 2) := by
  dsimp [avg, halfDiff]
  ring

private lemma fourth_lower_bound (c d D D' S wa wb ja jb : ℝ)
    (hc : 0 ≤ c) (hD : 0 ≤ D) (hDd : D ≤ d) (hD' : 0 ≤ D')
    (hD'hi : D' ≤ c * d / 2) (hS : 0 ≤ S) (hw : 0 ≤ avg wa wb) (hwab : wa ≤ wb) (hj : ja ≤ jb)
    (hZ : c * (d - D) - D' = (2 * D - d) * S - halfDiff wa wb) :
    d ^ 2 / 3 * avg wa wb ≤
      avg wa wb * ((d - 2 * D) ^ 2 + 2 * D ^ 2) - 4 * D * halfDiff ja jb +
      (d - D) * D * (d ^ 2 - 3 * d * D + 3 * D ^ 2) +
      (c * (d - D) - D') * (c * (d + D) + 3 * D') + c * S * (d ^ 2 - 2 * D ^ 2) := by
  have hd := hD.trans hDd
  have hw' : 0 ≤ avg wa wb * (6 * (D - d / 3) ^ 2) := by positivity
  have h1' : d ^ 2 / 3 * avg wa wb ≤ avg wa wb * ((d - 2 * D) ^ 2 + 2 * D ^ 2) := by
    linarith only [show avg wa wb * ((d - 2 * D) ^ 2 + 2 * D ^ 2) -
      d ^ 2 / 3 * avg wa wb = avg wa wb * (6 * (D - d / 3) ^ 2) by ring, hw']
  have h2' : 0 ≤ -(4 * D * halfDiff ja jb) := by
    apply neg_nonneg.mpr
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by unfold halfDiff; linarith)
  have h3' : 0 ≤ (d - D) * D * (d ^ 2 - 3 * d * D + 3 * D ^ 2) := by
    rw [show d ^ 2 - 3 * d * D + 3 * D ^ 2 = (d - 3 * D / 2) ^ 2 + 3 * D ^ 2 / 4 by ring]
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hDd) hD) (by positivity)
  have hZw : (2 * D - d) * S ≤ c * (d - D) - D' := by
    unfold halfDiff at hZ
    linarith
  have h4' : 0 ≤ (c * (d - D) - D') * (c * (d + D) + 3 * D') + c * S * (d ^ 2 - 2 * D ^ 2) := by
    by_cases hle : D ≤ d / 2
    · have hZZ : 0 ≤ c * (d - D) - D' := by
        have h := mul_nonneg hc (show 0 ≤ d / 2 - D by linarith)
        nlinarith only [hD'hi, h]
      exact add_nonneg (mul_nonneg hZZ (by positivity))
        (mul_nonneg (mul_nonneg hc hS) (by
          nlinarith only [mul_nonneg (show 0 ≤ d - 2 * D by linarith)
            (show 0 ≤ d + 2 * D by positivity), sq_nonneg D]))
    · have hzz : 0 ≤ (2 * D - d) * S := mul_nonneg (by linarith) hS
      have hm := mul_le_mul hZw
        (show c * (d + D) ≤ c * (d + D) + 3 * D' by linarith)
        (by positivity) (hzz.trans hZw)
      have he : (2 * D - d) * S * (c * (d + D)) +
          c * S * (d ^ 2 - 2 * D ^ 2) = c * S * d * D := by ring
      have hp : 0 ≤ c * S * d * D := by positivity
      linarith only [hm, he, hp]
  linarith only [h1', h2', h3', h4']

/-! ### A log-concave density and its transport -/

private def fExp (t v : ℝ) : ℝ := Real.exp (t * v) * (Real.cosh v - 1)

private lemma fExp_nonneg (t v : ℝ) : 0 ≤ fExp t v :=
  mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.one_le_cosh v))

private lemma fExp_pos {v : ℝ} (t : ℝ) (hv : 0 < v) : 0 < fExp t v := by
  apply mul_pos (Real.exp_pos _) (sub_pos.mpr _)
  simpa only [Real.cosh_zero, Real.cosh_lt_cosh, abs_zero, abs_of_pos hv] using
    (show Real.cosh 0 < Real.cosh v from Real.cosh_lt_cosh.2 (by simp [abs_of_pos hv, hv]))

private def leftMoment (n : ℕ) (t q : ℝ) : ℝ := ∫ v in 0..q, v ^ n * fExp t v

private lemma rightFTC {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    HasDerivAt (fun x => ∫ v in a..x, f v) (f b) b :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable (μ := volume) a b)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

private lemma leftMoment_deriv (n : ℕ) (t q : ℝ) :
    HasDerivAt (leftMoment n t) (q ^ n * fExp t q) q :=
  rightFTC (by unfold fExp; fun_prop) 0 q

private lemma leftMoment_nonneg (n : ℕ) {t q : ℝ} (hq : 0 ≤ q) : 0 ≤ leftMoment n t q := by
  exact intervalIntegral.integral_nonneg hq fun v hv =>
    mul_nonneg (pow_nonneg hv.1 _) (fExp_nonneg t v)

private lemma leftMass_pos {q : ℝ} (t : ℝ) (hq : 0 < q) : 0 < leftMoment 0 t q := by
  refine intervalIntegral.integral_pos hq (by unfold fExp; fun_prop)
    (fun v hv => mul_nonneg (pow_nonneg hv.1.le _) (fExp_nonneg t v))
    ⟨q, ⟨hq.le, le_rfl⟩, by simpa only [pow_zero, one_mul] using fExp_pos t hq⟩

private lemma cosh_sub_one (v : ℝ) : Real.cosh v - 1 = 2 * Real.sinh (v / 2) ^ 2 := by
  have h := Real.cosh_two_mul (x := v / 2)
  rw [show 2 * (v / 2) = v by ring, Real.cosh_sq] at h
  linarith only [h]

private lemma fExp_shift_compare {x y h : ℝ} (t : ℝ) (hh : 0 ≤ h) (hx : h ≤ x) (hxy : x ≤ y) :
    fExp t (x - h) * fExp t y ≤ fExp t (y - h) * fExp t x := by
  have he :
      Real.sinh ((y - h) / 2) * Real.sinh (x / 2) -
      Real.sinh ((x - h) / 2) * Real.sinh (y / 2) =
        Real.sinh (h / 2) * Real.sinh ((y - x) / 2) := by
    rw [show (y - h) / 2 = y / 2 - h / 2 by ring,
      show (x - h) / 2 = x / 2 - h / 2 by ring,
      show (y - x) / 2 = y / 2 - x / 2 by ring]
    simp only [Real.sinh_sub]
    ring
  have hA : 0 ≤ Real.sinh ((x - h) / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hB : 0 ≤ Real.sinh (y / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hP : 0 ≤ Real.sinh (h / 2) * Real.sinh ((y - x) / 2) :=
    mul_nonneg (Real.sinh_nonneg_iff.mpr (by linarith)) (Real.sinh_nonneg_iff.mpr (by linarith))
  have hs := (sq_le_sq₀ (mul_nonneg hA hB) (by linarith only [hP, he, mul_nonneg hA hB])).2
    (sub_nonneg.mp (he ▸ hP))
  unfold fExp
  simp only [cosh_sub_one]
  have hex : Real.exp (t * (x - h)) * Real.exp (t * y) =
      Real.exp (t * (y - h)) * Real.exp (t * x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  change _ ≤ _
  calc
    _ = (4 * (Real.exp (t * (x - h)) * Real.exp (t * y))) *
      (Real.sinh ((x - h) / 2) * Real.sinh (y / 2)) ^ 2 := by ring
    _ ≤ (4 * (Real.exp (t * (y - h)) * Real.exp (t * x))) *
      (Real.sinh ((y - h) / 2) * Real.sinh (x / 2)) ^ 2 := by
      rw [← hex]
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- Increasing left integral-to-density ratio for a tilted half of the
log-concave density. The sign follows from the hyperbolic subtraction formula. -/
private lemma tailRatio_mono (t : ℝ) :
    MonotoneOn (fun v => leftMoment 0 t v / fExp t v) (Set.Ioi 0) := by
  intro x hx y hy hxy
  change leftMoment 0 t x / fExp t x ≤ leftMoment 0 t y / fExp t y
  have hswap {v : ℝ} : (∫ u in 0..v, fExp t (v - u)) = leftMoment 0 t v := by
    simp [leftMoment]
  apply (div_le_div_iff₀ (fExp_pos t hx) (fExp_pos t hy)).2
  rw [← hswap, ← hswap, ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const]
  have hc (v r : ℝ) : Continuous (fun h => fExp t (v - h) * fExp t r) := by unfold fExp; fun_prop
  exact (intervalIntegral.integral_mono_on (le_of_lt hx) ((hc x y).intervalIntegrable (μ := volume) _ _)
    ((hc y x).intervalIntegrable (μ := volume) _ _) fun h hh => fExp_shift_compare t hh.1 hh.2 hxy).trans
    (intervalIntegral.integral_mono_interval le_rfl (le_of_lt hx) hxy
      (Eventually.of_forall fun h => mul_nonneg (fExp_nonneg t (y - h)) (fExp_nonneg t x))
      ((hc y x).intervalIntegrable (μ := volume) 0 y))

private def density (s q v : ℝ) : ℝ :=
  Real.exp (-s * v) * (Real.cosh (min v (2 * q - v)) - 1)

private def tilt (s q : ℝ) : ℝ := Real.exp (-2 * s * q)
private def mass (s q : ℝ) : ℝ := leftMoment 0 (-s) q + tilt s q * leftMoment 0 s q
private def firstMoment (s q : ℝ) : ℝ := leftMoment 1 (-s) q +
  tilt s q * (2 * q * leftMoment 0 s q - leftMoment 1 s q)
private def secondMoment (s q : ℝ) : ℝ := leftMoment 2 (-s) q +
  tilt s q * (4 * q ^ 2 * leftMoment 0 s q - 4 * q * leftMoment 1 s q + leftMoment 2 s q)
private def μ (s q : ℝ) : ℝ := firstMoment s q / mass s q
private def variance (s q : ℝ) : ℝ := secondMoment s q / mass s q - μ s q ^ 2

private lemma density_left {s q v : ℝ} (hv : v ≤ q) : density s q v = fExp (-s) v := by
  simp [density, fExp, min_eq_left (show v ≤ 2 * q - v by linarith)]

private lemma density_right {s q v : ℝ} (hv : q ≤ v) :
    density s q v = tilt s q * fExp s (2 * q - v) := by
  simp only [density, fExp, tilt, min_eq_right (show 2 * q - v ≤ v by linarith)]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

private lemma density_nonneg (s q v : ℝ) : 0 ≤ density s q v :=
  mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.one_le_cosh _))

private lemma density_pos {s q v : ℝ} (hv : v ∈ Set.Ioo 0 (2 * q)) : 0 < density s q v := by
  have hmin : 0 < min v (2 * q - v) := lt_min hv.1 (sub_pos.mpr hv.2)
  apply mul_pos (Real.exp_pos _) (sub_pos.mpr _)
  rw [← Real.cosh_zero, Real.cosh_lt_cosh, abs_zero, abs_of_pos hmin]
  exact hmin

private lemma density_continuous (s q : ℝ) : Continuous (density s q) := by
  unfold density
  fun_prop

private lemma mass_pos {s q : ℝ} (hq : 0 < q) : 0 < mass s q :=
  add_pos_of_pos_of_nonneg (leftMass_pos (-s) hq)
    (mul_nonneg (Real.exp_pos _).le (leftMoment_nonneg 0 hq.le))

private lemma density_split {s q : ℝ} (hq : 0 ≤ q) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ v in 0..(2 * q), g v * density s q v) =
      (∫ v in 0..q, g v * fExp (-s) v) +
        tilt s q * (∫ v in 0..q, g (2 * q - v) * fExp s v) := by
  have hc : Continuous (fun v => g v * density s q v) := hg.mul (density_continuous s q)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 q)
    (hc.intervalIntegrable (μ := volume) q (2 * q))]
  apply congrArg₂ (· + ·)
  · apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hq] at hv
    change g v * density s q v = g v * fExp (-s) v
    rw [density_left hv.2]
  · rw [← intervalIntegral.integral_const_mul]
    have hswap := intervalIntegral.integral_comp_sub_left
      (fun v => tilt s q * (g v * fExp s (2 * q - v))) (a := 0) (b := q) (2 * q)
    simp only [show 2 * q - q = q by ring, sub_zero,
      show ∀ v : ℝ, 2 * q - (2 * q - v) = v by intro v; ring] at hswap
    rw [hswap]
    have hq₂ : q ≤ 2 * q := by linarith
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hq₂] at hv
    change g v * density s q v = tilt s q * (g v * fExp s (2 * q - v))
    rw [density_right hv.1]
    ring

private lemma mass_integral {s q : ℝ} (hq : 0 ≤ q) :
    (∫ v in 0..(2 * q), density s q v) = mass s q := by
  simpa only [one_mul, leftMoment, pow_zero, mass] using
    (density_split (s := s) hq (continuous_const (y := (1 : ℝ))))

private lemma firstMoment_integral {s q : ℝ} (hq : 0 ≤ q) :
    (∫ v in 0..(2 * q), v * density s q v) = firstMoment s q := by
  have hh := density_split (s := s) hq continuous_id
  simp only [id_eq] at hh
  rw [hh]
  unfold firstMoment leftMoment
  simp only [pow_one, pow_zero, one_mul]
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub
    ((show Continuous (fun v => 2 * q * fExp s v) by unfold fExp; fun_prop).intervalIntegrable (μ := volume) _ _)
    ((show Continuous (fun v => v * fExp s v) by unfold fExp; fun_prop).intervalIntegrable (μ := volume) _ _),
    intervalIntegral.integral_const_mul]

private lemma secondMoment_integral {s q : ℝ} (hq : 0 ≤ q) :
    (∫ v in 0..(2 * q), v ^ 2 * density s q v) = secondMoment s q := by
  have hh := density_split (s := s) hq (show Continuous (fun v : ℝ => v ^ 2) from continuous_id.pow 2)
  rw [hh]
  unfold secondMoment leftMoment
  simp only [pow_one, pow_zero, one_mul]
  have hf : Continuous (fExp s) := by unfold fExp; fun_prop
  have h₁ := (hf.const_mul (4 * q ^ 2)).intervalIntegrable (μ := volume) 0 q
  have hf1 : Continuous (fun v => v * fExp s v) := continuous_id.mul hf
  have h₂ := (hf1.const_mul (4 * q)).intervalIntegrable (μ := volume) 0 q
  have hf2 : Continuous (fun v => v ^ 2 * fExp s v) := (continuous_id.pow 2).mul hf
  have h₃ := hf2.intervalIntegrable (μ := volume) 0 q
  have hc : (∫ v in 0..q, (2 * q - v) ^ 2 * fExp s v) =
      ∫ v in 0..q, (4 * q ^ 2 * fExp s v - (4 * q) * (v * fExp s v)) + v ^ 2 * fExp s v := by
    apply intervalIntegral.integral_congr
    intro v _
    ring
  rw [hc, intervalIntegral.integral_add (h₁.sub h₂) h₃, intervalIntegral.integral_sub h₁ h₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

private lemma tilt_mul_fExp (s q : ℝ) : tilt s q * fExp s q = fExp (-s) q := by
  simpa only [show 2 * q - q = q by ring] using
    (density_right (s := s) (q := q) (v := q) le_rfl).symm.trans (density_left le_rfl)

private def massRate (s q : ℝ) : ℝ := 2 * fExp (-s) q - 2 * s * tilt s q * leftMoment 0 s q
private def fluxRate (s q : ℝ) : ℝ := massRate s q / mass s q

private lemma tilt_deriv (s q : ℝ) : HasDerivAt (tilt s) (-2 * s * tilt s q) q := by
  convert ((hasDerivAt_id q).const_mul (-2 * s)).exp using 1
  · rfl
  · simp only [id_eq, mul_one, tilt]
    ring

private lemma mass_deriv (s q : ℝ) : HasDerivAt (mass s) (massRate s q) q := by
  convert (leftMoment_deriv 0 (-s) q).add
    ((tilt_deriv s q).mul (leftMoment_deriv 0 s q)) using 1
  · rfl
  · simp only [pow_zero, one_mul, massRate]
    linear_combination -(tilt_mul_fExp s q)

private lemma massRate_nonneg {s q : ℝ} (hq : 0 < q) : 0 ≤ massRate s q := by
  have hder (v : ℝ) : HasDerivAt (fExp s) (s * fExp s v + Real.exp (s * v) * Real.sinh v) v := by
    convert (((hasDerivAt_id v).const_mul s).exp).mul
      ((Real.hasDerivAt_cosh v).sub_const 1) using 1
    · rfl
    · simp only [id_eq, fExp]
      ring
  have hi (r : ℝ) : Continuous (fExp r) := by unfold fExp; fun_prop
  have h₂ : Continuous (fun v : ℝ => Real.exp (s * v) * Real.sinh v) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hder v)
    (((hi s).const_mul s).add h₂ |>.intervalIntegrable (μ := volume) 0 q)
  rw [intervalIntegral.integral_add (((hi s).const_mul s).intervalIntegrable (μ := volume) 0 q)
    (h₂.intervalIntegrable (μ := volume) 0 q), intervalIntegral.integral_const_mul] at hh
  have he : (∫ v in 0..q, fExp s v) = leftMoment 0 s q := by simp [leftMoment]
  rw [he, show fExp s 0 = 0 by simp [fExp], sub_zero] at hh
  have hn : 0 ≤ ∫ v in 0..q, Real.exp (s * v) * Real.sinh v :=
    intervalIntegral.integral_nonneg hq.le fun v hv =>
      mul_nonneg (Real.exp_pos _).le (Real.sinh_nonneg_iff.mpr hv.1)
  unfold massRate
  rw [← tilt_mul_fExp]
  have hl : 0 ≤ fExp s q - s * leftMoment 0 s q := by linarith only [hh, hn]
  nlinarith only [mul_nonneg (show 0 ≤ tilt s q from (Real.exp_pos _).le) hl]

private def rightFirst (s q : ℝ) : ℝ := tilt s q * (2 * q * leftMoment 0 s q - leftMoment 1 s q)
private def rightSecond (s q : ℝ) : ℝ :=
  tilt s q * (4 * q ^ 2 * leftMoment 0 s q - 4 * q * leftMoment 1 s q + leftMoment 2 s q)

private lemma firstMoment_deriv (s q : ℝ) :
    HasDerivAt (firstMoment s) (2 * q * fExp (-s) q - 2 * s * rightFirst s q +
      2 * tilt s q * leftMoment 0 s q) q := by
  convert (leftMoment_deriv 1 (-s) q).add ((tilt_deriv s q).mul
    ((((hasDerivAt_id q).const_mul 2).mul (leftMoment_deriv 0 s q)).sub
      (leftMoment_deriv 1 s q))) using 1
  · rfl
  · simp only [id_eq, pow_zero, pow_one, one_mul, Pi.mul_apply, Pi.sub_apply, rightFirst]
    linear_combination -q * (tilt_mul_fExp s q)

private lemma secondMoment_deriv (s q : ℝ) :
    HasDerivAt (secondMoment s) (2 * q ^ 2 * fExp (-s) q - 2 * s * rightSecond s q +
      4 * rightFirst s q) q := by
  convert (leftMoment_deriv 2 (-s) q).add ((tilt_deriv s q).mul
    (((((hasDerivAt_id q).pow 2).const_mul 4).mul (leftMoment_deriv 0 s q)).sub
      (((hasDerivAt_id q).const_mul 4).mul (leftMoment_deriv 1 s q)) |>.add
      (leftMoment_deriv 2 s q))) using 1
  · rfl
  · simp only [id_eq, pow_zero, pow_one, one_mul, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply,
      rightFirst, rightSecond]
    linear_combination -q ^ 2 * (tilt_mul_fExp s q)

private def fluxL (s q v : ℝ) : ℝ := fluxRate s q * leftMoment 0 (-s) v
private def fluxR (s q v : ℝ) : ℝ :=
  2 * (tilt s q * fExp s (2 * q - v)) -
    (2 * s + fluxRate s q) * (tilt s q * leftMoment 0 s (2 * q - v))
private def flux (s q v : ℝ) : ℝ := if v ≤ q then fluxL s q v else fluxR s q v

private lemma fluxRate_mul_mass {s q : ℝ} (hq : 0 < q) : fluxRate s q * mass s q = massRate s q :=
  div_mul_cancel₀ _ (mass_pos hq).ne'

private lemma flux_agrees {s q : ℝ} (hq : 0 < q) : fluxL s q q = fluxR s q q := by
  have h := fluxRate_mul_mass (s := s) hq
  unfold mass massRate at h
  rw [fluxL, fluxR, show 2 * q - q = q by ring, tilt_mul_fExp]
  linarith only [h]

private lemma flux_continuous {s q : ℝ} (hq : 0 < q) : Continuous (flux s q) := by
  change Continuous (Set.piecewise (Set.Iic q) (fluxL s q) (fluxR s q))
  have h (t : ℝ) : Continuous (leftMoment 0 t) :=
    continuous_iff_continuousAt.mpr fun v => (leftMoment_deriv 0 t v).continuousAt
  apply Continuous.piecewise
  · intro v hv
    obtain rfl : v = q := frontier_Iic_subset q hv
    exact flux_agrees hq
  · unfold fluxL
    fun_prop
  · unfold fluxR fExp
    fun_prop

private def drift (s q v : ℝ) : ℝ := flux s q v / density s q v

private lemma drift_left {s q v : ℝ} (hv : v ≤ q) :
    drift s q v = fluxRate s q * (leftMoment 0 (-s) v / fExp (-s) v) := by
  rw [drift, flux, ite_eq_left hv, density_left hv, fluxL, mul_div_assoc]

private lemma drift_right {s q v : ℝ} (hq : 0 < q) (hvq : q ≤ v) (hv : v < 2 * q) :
    drift s q v = 2 - (2 * s + fluxRate s q) * (leftMoment 0 s (2 * q - v) / fExp s (2 * q - v)) := by
  have hf : flux s q v = fluxR s q v := by
    rcases hvq.eq_or_lt with h | h
    · subst v
      rw [flux, ite_eq_left le_rfl, flux_agrees hq]
    · exact ite_eq_right h.not_ge
  rw [drift, hf, fluxR, density_right hvq]
  field_simp [(show tilt s q ≠ 0 from (Real.exp_pos _).ne'), (fExp_pos s (sub_pos.mpr hv)).ne']

private lemma drift_mono {s q : ℝ} (hs : 0 ≤ s) (hq : 0 < q) :
    MonotoneOn (drift s q) (Set.Ioo 0 (2 * q)) := by
  have hRate : 0 ≤ fluxRate s q := div_nonneg (massRate_nonneg hq) (mass_pos hq).le
  have hL {v w : ℝ} (hv : 0 < v) (hvw : v ≤ w) (hw : w ≤ q) :
      drift s q v ≤ drift s q w := by
    rw [drift_left (hvw.trans hw), drift_left hw]
    exact mul_le_mul_of_nonneg_left (tailRatio_mono (-s) hv (hv.trans_le hvw) hvw) hRate
  have hR {v w : ℝ} (hv : q ≤ v) (hvw : v ≤ w) (hw : w < 2 * q) :
      drift s q v ≤ drift s q w := by
    rw [drift_right hq hv (hvw.trans_lt hw), drift_right hq (hv.trans hvw) hw]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left
      (tailRatio_mono s (sub_pos.mpr hw) (sub_pos.mpr (hvw.trans_lt hw)) (sub_le_sub_left hvw _))
      (by linarith)) _
  intro v hv w hw hvw
  rcases le_total w q with hl | hr
  · exact hL hv.1 hvw hl
  rcases le_total v q with hl | hr'
  · exact (hL hv.1 hl le_rfl).trans (hR le_rfl hr hw.2)
  · exact hR hr' hvw hw.2

private lemma drift_nonneg {s q v : ℝ} (hs : 0 ≤ s) (hq : 0 < q) (hv : v ∈ Set.Ioo 0 (2 * q)) :
    0 ≤ drift s q v := by
  have hL (x : ℝ) (hx : 0 < x) (hxq : x ≤ q) : 0 ≤ drift s q x := by
    rw [drift_left hxq]
    exact mul_nonneg (div_nonneg (massRate_nonneg hq) (mass_pos hq).le)
      (div_nonneg (leftMoment_nonneg 0 hx.le) (fExp_pos (-s) hx).le)
  rcases le_total v q with h | h
  · exact hL v hv.1 h
  · exact (hL q hq le_rfl).trans (drift_mono hs hq ⟨hq, by linarith⟩ hv h)

private lemma flux_eq_mul {s q v : ℝ} (hv : v ∈ Set.Ioo 0 (2 * q)) :
    flux s q v = drift s q v * density s q v :=
  (div_mul_cancel₀ _ (density_pos hv).ne').symm

private lemma beta_moment {t q : ℝ} (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * (∫ v in 0..q, v ^ n * leftMoment 0 t v) =
      q ^ (n + 1) * leftMoment 0 t q - leftMoment (n + 1) t q := by
  have hD (v : ℝ) : HasDerivAt (fun v => v ^ (n + 1) * leftMoment 0 t v)
      (v ^ (n + 1) * fExp t v + ((n + 1 : ℕ) : ℝ) * (v ^ n * leftMoment 0 t v)) v := by
    convert ((hasDerivAt_id v).pow (n + 1)).mul (leftMoment_deriv 0 t v) using 1
    · rfl
    · simp only [pow_zero, one_mul, id_eq, Nat.add_sub_cancel, Pi.pow_apply]
      ring
  have hf : Continuous (fun v : ℝ => v ^ (n + 1) * fExp t v) := by unfold fExp; fun_prop
  have hB : Continuous (leftMoment 0 t) :=
    continuous_iff_continuousAt.mpr fun v => (leftMoment_deriv 0 t v).continuousAt
  have hg : Continuous (fun v : ℝ => ((n + 1 : ℕ) : ℝ) * (v ^ n * leftMoment 0 t v)) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hD v)
    ((hf.add hg).intervalIntegrable (μ := volume) 0 q)
  rw [intervalIntegral.integral_add (hf.intervalIntegrable (μ := volume) 0 q) (hg.intervalIntegrable (μ := volume) 0 q),
    intervalIntegral.integral_const_mul] at he
  change leftMoment (n + 1) t q + _ = _ at he
  simp only [show leftMoment 0 t 0 = 0 by simp [leftMoment], mul_zero, sub_zero] at he
  linarith only [he]

private lemma flux_split {s q : ℝ} (hq : 0 < q) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ v in 0..(2 * q), g v * flux s q v) =
      (∫ v in 0..q, g v * fluxL s q v) +
      (∫ v in 0..q, g (2 * q - v) *
        (2 * (tilt s q * fExp s v) - (2 * s + fluxRate s q) * (tilt s q * leftMoment 0 s v))) := by
  have hc : Continuous (fun v => g v * flux s q v) := hg.mul (flux_continuous hq)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 q)
    (hc.intervalIntegrable (μ := volume) q (2 * q))]
  apply congrArg₂ (· + ·)
  · apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hq.le] at hv
    change g v * flux s q v = g v * fluxL s q v
    rw [flux, ite_eq_left hv.2]
  · have hswap := intervalIntegral.integral_comp_sub_left
      (fun v => g v * (2 * (tilt s q * fExp s (2 * q - v)) -
        (2 * s + fluxRate s q) * (tilt s q * leftMoment 0 s (2 * q - v)))) (a := 0) (b := q) (2 * q)
    simp only [show 2 * q - q = q by ring, sub_zero,
      show ∀ v : ℝ, 2 * q - (2 * q - v) = v by intro v; ring] at hswap
    rw [hswap]
    have hq₂ : q ≤ 2 * q := by linarith
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hq₂] at hv
    have hR : flux s q v = fluxR s q v := by
      rcases hv.1.eq_or_lt with h | h
      · subst v
        rw [flux, ite_eq_left le_rfl, flux_agrees hq]
      · exact ite_eq_right h.not_ge
    change g v * flux s q v = g v * fluxR s q v
    rw [hR]

private lemma interval_linear {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (a b x y : ℝ) :
    (∫ v in a..b, x * f v - y * g v) =
      x * (∫ v in a..b, f v) - y * (∫ v in a..b, g v) := by
  rw [intervalIntegral.integral_sub ((hf.const_mul x).intervalIntegrable (μ := volume) a b)
    ((hg.const_mul y).intervalIntegrable (μ := volume) a b), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

private lemma flux_moment_zero {s q : ℝ} (hq : 0 < q) :
    (∫ v in 0..(2 * q), flux s q v) =
      2 * q * fExp (-s) q - 2 * s * rightFirst s q +
        2 * tilt s q * leftMoment 0 s q - fluxRate s q * firstMoment s q := by
  have hb (t : ℝ) : Continuous (leftMoment 0 t) :=
    continuous_iff_continuousAt.mpr fun v => (leftMoment_deriv 0 t v).continuousAt
  have hf : Continuous (fExp s) := by unfold fExp; fun_prop
  have hh := flux_split (s := s) hq (continuous_const (y := (1 : ℝ)))
  simp only [one_mul] at hh
  have hR : (∫ v in 0..q, 2 * (tilt s q * fExp s v) -
      (2 * s + fluxRate s q) * (tilt s q * leftMoment 0 s v)) =
      (2 * tilt s q) * leftMoment 0 s q -
        ((2 * s + fluxRate s q) * tilt s q) * (∫ v in 0..q, leftMoment 0 s v) := by
    simpa only [mul_assoc, leftMoment, pow_zero, one_mul] using
      interval_linear hf (hb s) 0 q (2 * tilt s q) ((2 * s + fluxRate s q) * tilt s q)
  rw [hh, hR]
  unfold fluxL
  rw [intervalIntegral.integral_const_mul]
  have hl (t : ℝ) : (∫ v in 0..q, leftMoment 0 t v) =
      q * leftMoment 0 t q - leftMoment 1 t q := by
    simpa only [Nat.zero_add, Nat.cast_one, one_mul, pow_one, pow_zero] using beta_moment (t := t) (q := q) 0
  rw [hl (-s), hl s]
  have h := fluxRate_mul_mass (s := s) hq
  unfold mass massRate at h
  unfold rightFirst firstMoment
  linear_combination q * h

private lemma flux_moment_one {s q : ℝ} (hq : 0 < q) :
    2 * (∫ v in 0..(2 * q), v * flux s q v) =
      2 * q ^ 2 * fExp (-s) q - 2 * s * rightSecond s q +
        4 * rightFirst s q - fluxRate s q * secondMoment s q := by
  have hb (t : ℝ) : Continuous (leftMoment 0 t) :=
    continuous_iff_continuousAt.mpr fun v => (leftMoment_deriv 0 t v).continuousAt
  have hf : Continuous (fExp s) := by unfold fExp; fun_prop
  have hh := flux_split (s := s) hq continuous_id
  simp only [id_eq] at hh
  have hc (f : ℝ → ℝ) (h : Continuous f) :
      (∫ v in 0..q, (2 * q - v) * f v) =
        2 * q * (∫ v in 0..q, f v) - ∫ v in 0..q, v * f v := by
    simp_rw [sub_mul]
    simpa only [one_mul] using interval_linear h (show Continuous (fun v : ℝ => v * f v) from continuous_id.mul h) 0 q (2 * q) 1
  have hR : (∫ v in 0..q, (2 * q - v) * (2 * (tilt s q * fExp s v) -
       (2 * s + fluxRate s q) * (tilt s q * leftMoment 0 s v))) =
      (2 * tilt s q) * (∫ v in 0..q, (2 * q - v) * fExp s v) -
       ((2 * s + fluxRate s q) * tilt s q) * (∫ v in 0..q, (2 * q - v) * leftMoment 0 s v) := by
    have hm : Continuous (fun v : ℝ => 2 * q - v) := by fun_prop
    have hf' : Continuous (fun v => (2 * q - v) * fExp s v) := hm.mul hf
    have hb' : Continuous (fun v => (2 * q - v) * leftMoment 0 s v) := hm.mul (hb s)
    rw [← interval_linear hf' hb' 0 q]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp
    ring
  have hL : (∫ v in 0..q, v * fluxL s q v) =
      fluxRate s q * (∫ v in 0..q, v * leftMoment 0 (-s) v) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    unfold fluxL
    ring
  rw [hh, hL, hR, hc _ hf, hc _ (hb s)]
  have h0 : (∫ v in 0..q, fExp s v) = leftMoment 0 s q := by simp [leftMoment]
  have h1 : (∫ v in 0..q, v * fExp s v) = leftMoment 1 s q := by simp [leftMoment]
  have hl0 (t : ℝ) : (∫ v in 0..q, leftMoment 0 t v) =
      q * leftMoment 0 t q - leftMoment 1 t q := by
    simpa only [Nat.zero_add, Nat.cast_one, one_mul, pow_one, pow_zero] using beta_moment (t := t) (q := q) 0
  have hl1 (t : ℝ) : (∫ v in 0..q, v * leftMoment 0 t v) =
      (q ^ 2 * leftMoment 0 t q - leftMoment 2 t q) / 2 := by
    have h := beta_moment (t := t) (q := q) 1
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat, pow_one] at h
    linarith only [h]
  rw [h0, h1, hl0, hl1, hl1]
  have h := fluxRate_mul_mass (s := s) hq
  unfold mass massRate at h
  unfold rightFirst rightSecond secondMoment
  linear_combination (q ^ 2) * h

private lemma μ_deriv_q {s q : ℝ} (hq : 0 < q) :
    HasDerivAt (μ s) ((∫ v in 0..(2 * q), flux s q v) / mass s q) q := by
  convert (firstMoment_deriv s q).div (mass_deriv s q) (mass_pos hq).ne' using 1
  · rfl
  · rw [flux_moment_zero hq, fluxRate]
    field_simp [(mass_pos hq).ne']

private lemma variance_deriv_q {s q : ℝ} (hq : 0 < q) :
    HasDerivAt (variance s) ((2 / mass s q) *
      ((∫ v in 0..(2 * q), v * flux s q v) - μ s q * (∫ v in 0..(2 * q), flux s q v))) q := by
  convert ((secondMoment_deriv s q).div (mass_deriv s q) (mass_pos hq).ne').sub
    ((μ_deriv_q hq).pow 2) using 1
  · rfl
  · have hh := flux_moment_one (s := s) hq
    rw [fluxRate] at hh
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [(mass_pos hq).ne'] at hh ⊢
    linear_combination hh

private lemma μ_mem_support {s q : ℝ} (hq : 0 < q) : μ s q ∈ Set.Ioo 0 (2 * q) := by
  have hq₂ : 0 < 2 * q := by positivity
  have hf := density_continuous s q
  have hf1 := continuous_id.mul hf
  have hh : q ∈ Set.Ioo (0 : ℝ) (2 * q) := ⟨hq, by linarith⟩
  have h0 : 0 < ∫ v in 0..(2 * q), v * density s q v :=
    intervalIntegral.integral_pos hq₂ hf1.continuousOn
      (fun v hv => mul_nonneg hv.1.le (density_nonneg s q v))
      ⟨q, ⟨hh.1.le, hh.2.le⟩, mul_pos hq (density_pos hh)⟩
  have h1 : (∫ v in 0..(2 * q), v * density s q v) <
      ∫ v in 0..(2 * q), (2 * q) * density s q v :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hq₂ hf1.continuousOn
      (hf.const_mul _).continuousOn
      (fun v hv => mul_le_mul_of_nonneg_right hv.2 (density_nonneg s q v))
      ⟨q, ⟨hh.1.le, hh.2.le⟩, mul_lt_mul_of_pos_right hh.2 (density_pos hh)⟩
  rw [firstMoment_integral hq.le] at h0
  rw [intervalIntegral.integral_const_mul, mass_integral hq.le, firstMoment_integral hq.le] at h1
  exact ⟨div_pos h0 (mass_pos hq), (div_lt_iff₀ (mass_pos hq)).2 h1⟩

private lemma μ_mono {s : ℝ} (hs : 0 ≤ s) : MonotoneOn (μ s) (Set.Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun q hq => (μ_deriv_q hq).continuousAt.continuousWithinAt)
    (fun q hq => (μ_deriv_q (by simpa only [interior_Ioi, Set.mem_Ioi] using hq)).differentiableAt.differentiableWithinAt) ?_
  intro q hq
  rw [interior_Ioi] at hq
  rw [(μ_deriv_q hq).deriv]
  apply div_nonneg _ (mass_pos hq).le
  have hq₂ : 0 ≤ 2 * q := mul_nonneg (by norm_num) (le_of_lt hq)
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hq₂
    ((continuous_const (y := (0 : ℝ))).intervalIntegrable (μ := volume) 0 (2 * q))
    ((flux_continuous hq).intervalIntegrable (μ := volume) 0 (2 * q)) (fun v hv => by
      rw [flux_eq_mul hv]
      exact mul_nonneg (drift_nonneg hs hq hv) (density_nonneg s q v))
  simpa only [intervalIntegral.integral_zero] using h

/-- The covariance of v and the increasing drift is nonnegative. Centering
the drift at the mean gives a pointwise nonnegative integrand. -/
private lemma covariance_nonneg {s q : ℝ} (hs : 0 ≤ s) (hq : 0 < q) :
    0 ≤ (∫ v in 0..(2 * q), v * flux s q v) - μ s q * (∫ v in 0..(2 * q), flux s q v) := by
  let m := μ s q
  let C := drift s q m
  have hm : m ∈ Set.Ioo 0 (2 * q) := μ_mem_support hq
  have hq₂ : 0 ≤ 2 * q := mul_nonneg (by norm_num) (le_of_lt hq)
  have hpoint (v : ℝ) (hv : v ∈ Set.Ioo 0 (2 * q)) :
      C * (v * density s q v - m * density s q v) ≤
      v * flux s q v - m * flux s q v := by
    rw [flux_eq_mul hv]
    have hprod : 0 ≤ (v - m) * (drift s q v - C) := by
      rcases le_total v m with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
          (sub_nonpos.mpr (drift_mono hs hq hv hm h))
      · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (drift_mono hs hq hm hv h))
    nlinarith only [mul_nonneg hprod (density_nonneg s q v)]
  have hf := density_continuous s q
  have hF := flux_continuous (s := s) hq
  have hC := (((continuous_id.mul hf).sub (hf.const_mul m)).const_mul C).intervalIntegrable (μ := volume) 0 (2 * q)
  have hG := ((continuous_id.mul hF).sub (hF.const_mul m)).intervalIntegrable (μ := volume) 0 (2 * q)
  have hg := intervalIntegral.integral_mono_on_of_le_Ioo hq₂ hC hG hpoint
  have hlin (f : ℝ → ℝ) (hf : Continuous f) :
      (∫ v in 0..(2 * q), v * f v - m * f v) =
        (∫ v in 0..(2 * q), v * f v) - m * (∫ v in 0..(2 * q), f v) := by
    have hf' : Continuous (fun v => v * f v) := continuous_id.mul hf
    simpa only [one_mul] using interval_linear hf' hf 0 (2 * q) 1 m
  rw [intervalIntegral.integral_const_mul] at hg
  change C * (∫ v in 0..(2 * q), v * density s q v - m * density s q v) ≤
    (∫ v in 0..(2 * q), v * flux s q v - m * flux s q v) at hg
  rw [hlin _ hf, hlin _ hF, mass_integral hq.le, firstMoment_integral hq.le] at hg
  have h0 : m * mass s q = firstMoment s q := div_mul_cancel₀ _ (mass_pos hq).ne'
  rw [h0, sub_self, mul_zero] at hg
  exact hg

private lemma variance_mono {s : ℝ} (hs : 0 ≤ s) : MonotoneOn (variance s) (Set.Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun q hq => (variance_deriv_q hq).continuousAt.continuousWithinAt)
    (fun q hq => (variance_deriv_q (by simpa only [interior_Ioi, Set.mem_Ioi] using hq)).differentiableAt.differentiableWithinAt) ?_
  intro q hq
  rw [interior_Ioi] at hq
  rw [(variance_deriv_q hq).deriv]
  exact mul_nonneg (div_nonneg (by norm_num) (mass_pos hq).le) (covariance_nonneg hs hq)

private lemma interval_param_deriv {F G : ℝ → ℝ → ℝ} {s T : ℝ} (hT : 0 ≤ T)
    (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G))
    (hd : ∀ u v, HasDerivAt (fun u => F u v) (G u v) u) :
    HasDerivAt (fun u => ∫ v in 0..T, F u v) (∫ v in 0..T, G s v) s := by
  let m := volume.restrict (Set.Ioc 0 T)
  have hC : ∃ C : ℝ, ∀ u ∈ Set.Icc (s - 1) (s + 1), ∀ v ∈ Set.Icc 0 T, ‖G u v‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Set.Icc (s - 1) (s + 1) ×ˢ Set.Icc 0 T)).bddAbove_image hG.norm.continuousOn
    exact ⟨C, fun u hu v hv => hC ⟨(u, v), ⟨hu, hv⟩, rfl⟩⟩
  obtain ⟨C, hC⟩ := hC
  have hFU (u : ℝ) : Continuous (F u) := hF.comp (continuous_const.prodMk continuous_id)
  have hGU (u : ℝ) : Continuous (G u) := hG.comp (continuous_const.prodMk continuous_id)
  have hbound : ∀ᵐ v ∂m, ∀ u ∈ Set.Ioo (s - 1) (s + 1), ‖G u v‖ ≤ C := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Set.Ioc 0 T) measurableSet_Ioc] with v hv
    exact fun u hu => hC u ⟨hu.1.le, hu.2.le⟩ v ⟨hv.1.le, hv.2⟩
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := m) (F := F) (F' := G) (x₀ := s) (s := Set.Ioo (s - 1) (s + 1))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun u => (hFU u).aestronglyMeasurable)
    ((hFU s).intervalIntegrable (μ := volume) 0 T).1
    (hGU s).aestronglyMeasurable hbound
    ((continuous_const (y := C)).intervalIntegrable (μ := volume) 0 T).1
    (Eventually.of_forall fun v u _ => hd u v)
  simpa only [intervalIntegral.integral_of_le hT, m] using h.2

private lemma mass_deriv_s {s q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun s => mass s q) (-firstMoment s q) s := by
  have hG : Continuous (Function.uncurry (fun s v => -(v * density s q v))) := by
    unfold Function.uncurry density
    fun_prop
  have hh := interval_param_deriv (s := s) (T := 2 * q) (F := fun s v => density s q v)
    (G := fun s v => -(v * density s q v)) (by positivity)
    (by unfold Function.uncurry density; fun_prop) hG (by
      intro t v
      have hd := (((hasDerivAt_id t).const_mul (-v)).exp).mul_const
        (Real.cosh (min v (2 * q - v)) - 1)
      convert hd using 1
      · funext u; simp only [id_eq, density, show -v * u = -u * v by ring]
      · unfold density; simp only [id_eq, mul_one]
        rw [show -v * t = -t * v by ring]
        ring)
  simpa only [mass_integral hq.le, intervalIntegral.integral_neg, firstMoment_integral hq.le] using hh

private lemma firstMoment_deriv_s {s q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun s => firstMoment s q) (-secondMoment s q) s := by
  have hh := interval_param_deriv (s := s) (T := 2 * q) (F := fun s v => v * density s q v)
    (G := fun s v => -(v ^ 2 * density s q v)) (by positivity)
    (by unfold Function.uncurry density; fun_prop) (by unfold Function.uncurry density; fun_prop) (by
      intro t v
      have hd := ((((hasDerivAt_id t).const_mul (-v)).exp).mul_const
        (Real.cosh (min v (2 * q - v)) - 1)).const_mul v
      convert hd using 1
      · funext u; simp only [id_eq, density, show -v * u = -u * v by ring]
      · unfold density; simp only [id_eq, mul_one]
        rw [show -v * t = -t * v by ring]
        ring)
  simpa only [firstMoment_integral hq.le, intervalIntegral.integral_neg, secondMoment_integral hq.le] using hh

private lemma μ_deriv_s {s q : ℝ} (hq : 0 < q) : HasDerivAt (fun s => μ s q) (-variance s q) s := by
  convert (firstMoment_deriv_s hq).div (mass_deriv_s hq) (mass_pos hq).ne' using 1
  · rfl
  · unfold variance μ
    field_simp [(mass_pos hq).ne']
    ring

private lemma leftMass_formula {t : ℝ} (q : ℝ) (h₀ : t ≠ 0) (h₁ : t + 1 ≠ 0)
    (h₂ : t - 1 ≠ 0) :
    leftMoment 0 t q = (Real.exp ((t + 1) * q) - 1) / (2 * (t + 1)) +
      (Real.exp ((t - 1) * q) - 1) / (2 * (t - 1)) - (Real.exp (t * q) - 1) / t := by
  let F (v : ℝ) := Real.exp ((t + 1) * v) / (2 * (t + 1)) +
    Real.exp ((t - 1) * v) / (2 * (t - 1)) - Real.exp (t * v) / t
  have hd (v : ℝ) : HasDerivAt F (fExp t v) v := by
    have hh (u : ℝ) := (((hasDerivAt_id v).const_mul u).exp)
    convert (((hh (t + 1)).div_const (2 * (t + 1))).add
      ((hh (t - 1)).div_const (2 * (t - 1)))).sub ((hh t).div_const t) using 1
    · rfl
    · simp only [id_eq, mul_one]
      unfold fExp
      rw [show (t + 1) * v = t * v + v by ring, show (t - 1) * v = t * v + -v by ring]
      simp only [Real.exp_add, Real.cosh_eq]
      field_simp [h₀, h₁, h₂]
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
    ((show Continuous (fExp t) by unfold fExp; fun_prop).intervalIntegrable (μ := volume) 0 q)
  simpa only [leftMoment, pow_zero, one_mul] using hh.trans (by
    unfold F
    simp only [mul_zero, Real.exp_zero]
    ring)

private def massFactor (s : ℝ) : ℝ := s * (s - 1) * (s + 1) / 2

private lemma H_mass {s : ℝ} (hs : 1 < s) (q : ℝ) :
    H q s = massFactor s * Real.exp (s * q) * mass s q := by
  unfold mass massFactor tilt H
  rw [leftMass_formula q (t := -s) (by linarith) (by linarith) (by linarith),
    leftMass_formula q (t := s) (by linarith) (by linarith) (by linarith)]
  rw [show (-s + 1) * q = -(s * q) + q by ring,
    show (-s - 1) * q = -(s * q) + -q by ring, show (-s) * q = -(s * q) by ring,
    show (s + 1) * q = s * q + q by ring, show (s - 1) * q = s * q + -q by ring,
    show -2 * s * q = -(s * q + s * q) by ring, Real.sinh_eq, Real.sinh_eq]
  simp only [Real.exp_add, Real.exp_neg]
  field_simp [(show s ≠ 0 by linarith), (show s - 1 ≠ 0 by linarith),
    (show s + 1 ≠ 0 by linarith), (show -s + 1 ≠ 0 by linarith),
    (show -s - 1 ≠ 0 by linarith), (Real.exp_pos q).ne', (Real.exp_pos (s * q)).ne']
  ring

private lemma p_mass {q s : ℝ} (hq : 0 < q) (hs : 1 < s) :
    p q s = q + deriv massFactor s / massFactor s - μ s q := by
  have hF : HasDerivAt massFactor (deriv massFactor s) s :=
    (show DifferentiableAt ℝ massFactor s by unfold massFactor; fun_prop).hasDerivAt
  have hex := (((hasDerivAt_id s).mul_const q).exp)
  have hh := (hF.mul hex).mul (mass_deriv_s (s := s) hq)
  have he : (fun t => massFactor t * Real.exp (t * q) * mass t q) =ᶠ[𝓝 s] H q := by
    filter_upwards [lt_mem_nhds hs] with t ht using (H_mass ht q).symm
  have h := (H_deriv_s q s).unique (hh.congr_of_eventuallyEq he.symm)
  change h₁ q s = _ at h
  have hF₀ : 0 < massFactor s :=
    div_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) (by norm_num)
  unfold p μ
  rw [h, H_mass hs q]
  simp only [id_eq, one_mul, Pi.mul_apply]
  field_simp [hF₀.ne', (mass_pos hq).ne', (Real.exp_pos (s * q)).ne']
  ring

/-- The first moment bounds D from above. Differentiating the difference of
logarithmic derivatives identifies D' with half the variance difference. -/
private lemma p_halfDiff_transport {a b s : ℝ} (hb : 0 < b) (hba : b ≤ a) (hs : 1 < s) :
    halfDiff (p a s) (p b s) ≤ halfDiff a b ∧ 0 ≤ halfDiff (p₁ a s) (p₁ b s) := by
  have ha := hb.trans_le hba
  have hs₀ : 0 ≤ s := by linarith
  have he (t : ℝ) (ht : 1 < t) :
      p a t - p b t = (a - b) + (μ t b - μ t a) := by
    rw [p_mass ha ht, p_mass hb ht]
    ring
  constructor
  · unfold halfDiff
    linarith only [he s hs, μ_mono hs₀ hb ha hba]
  · have hder := ((μ_deriv_s (s := s) hb).sub (μ_deriv_s (s := s) ha)).const_add (a - b)
    have h := ((p_deriv ha hs).sub (p_deriv hb hs)).unique
      (hder.congr_of_eventuallyEq (by filter_upwards [lt_mem_nhds hs] with t ht using he t ht))
    change p₁ a s - p₁ b s = -variance s b - -variance s a at h
    unfold halfDiff
    linarith only [h, variance_mono hs₀ hb ha hba]

/-! ### Comparison of power series -/

private lemma hasSum_drop (f : ℕ → ℝ) (k : ℕ) (r : ℝ) (h : HasSum f r) :
    HasSum (fun i => f (i + k)) (r - ∑ i ∈ range k, f i) :=
  (hasSum_nat_add_iff' (G := ℝ) (g := r) (f := f) k).mpr h

/-- Pairing the terms `(i,j)` and `(j,i)` in the product of two series
transfers the order of the coefficient ratios to the order of the sums. -/
private lemma series_cross_le {α β : ℕ → ℝ} {e : ℕ → ℕ}
    (he : Monotone e) (hc : ∀ i j, i ≤ j → α i * β j ≤ α j * β i)
    {x y ax ay bx b_y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hax : HasSum (fun i => α i * x ^ e i) ax)
    (hay : HasSum (fun i => α i * y ^ e i) ay)
    (hbx : HasSum (fun i => β i * x ^ e i) bx)
    (hby : HasSum (fun i => β i * y ^ e i) b_y) : ax * b_y ≤ ay * bx := by
  have hpow (i j : ℕ) (hij : i ≤ j) : x ^ e j * y ^ e i ≤ y ^ e j * x ^ e i := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (he hij)
    rw [hk, pow_add, pow_add]
    calc
      x ^ e i * x ^ k * y ^ e i = (x ^ e i * y ^ e i) * x ^ k := by ring
      _ ≤ (x ^ e i * y ^ e i) * y ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _) (mul_nonneg (pow_nonneg hx _) (pow_nonneg (hx.trans hxy) _))
      _ = y ^ e i * y ^ k * x ^ e i := by ring
  have hterm (i j : ℕ) :
      0 ≤ (α j * β i - α i * β j) * (y ^ e j * x ^ e i - x ^ e j * y ^ e i) := by
    rcases le_total i j with h | h
    · exact mul_nonneg (sub_nonneg.mpr (hc i j h)) (sub_nonneg.mpr (hpow i j h))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hc j i h)) (by
        linarith only [hpow j i h])
  apply le_of_tendsto_of_tendsto (hax.tendsto_sum_nat.mul hby.tendsto_sum_nat)
    (hay.tendsto_sum_nat.mul hbx.tendsto_sum_nat)
  apply Eventually.of_forall
  intro n
  have hs := Finset.sum_nonneg (s := range n) fun i _ =>
    Finset.sum_nonneg (s := range n) fun j _ => hterm i j
  have eq (i j : ℕ) :
      (α j * β i - α i * β j) * (y ^ e j * x ^ e i - x ^ e j * y ^ e i) =
      β i * x ^ e i * (α j * y ^ e j) - β i * y ^ e i * (α j * x ^ e j) -
      (α i * x ^ e i * (β j * y ^ e j) - α i * y ^ e i * (β j * x ^ e j)) := by ring
  simp only [eq, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hs
  linarith only [hs]

private def L (x : ℝ) : ℝ := x * Real.cosh x - Real.sinh x
private def kRatio (x : ℝ) : ℝ := x ^ 2 * Real.sinh x / L x

private lemma L_pos {x : ℝ} (hx : 0 < x) : 0 < L x := sinh_mul_sub_pos hx

private lemma L_deriv (x : ℝ) : HasDerivAt L (x * Real.sinh x) x := by
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
    (Real.hasDerivAt_sinh x) using 1
  · rfl
  · simp only [id_eq, one_mul]
    ring

private lemma sinh_tail (x : ℝ) :
    HasSum (fun i : ℕ => x ^ (2 * i + 3) / (Nat.factorial (2 * i + 3) : ℝ))
      (Real.sinh x - x) := by
  let f (i : ℕ) := x ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ)
  have ht := hasSum_drop f 1 (Real.sinh x) (Real.hasSum_sinh x)
  have h0 : (∑ i ∈ range 1, f i) = x := by simp [f]
  rw [h0] at ht
  refine ht.congr_fun fun i => ?_
  dsimp only [f]
  rw [show 2 * (i + 1) + 1 = 2 * i + 3 by omega]

private lemma L_series (x : ℝ) :
    HasSum (fun i : ℕ => ((2 * i + 2 : ℕ) : ℝ) / (Nat.factorial (2 * i + 3) : ℝ) *
      x ^ (2 * i + 3)) (L x) := by
  let f (i : ℕ) := x * (x ^ (2 * i) / (Nat.factorial (2 * i) : ℝ)) -
    x ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ)
  have hh : HasSum f (L x) := ((Real.hasSum_cosh x).mul_left x).sub (Real.hasSum_sinh x)
  have ht := hasSum_drop f 1 (L x) hh
  have h0 : (∑ i ∈ range 1, f i) = 0 := by simp [f]
  rw [h0, sub_zero] at ht
  apply ht.congr_fun
  intro i
  dsimp only [f]
  let n := 2 * i + 2
  have hn : 2 * (i + 1) = n := by dsimp [n]; omega
  have hn' : 2 * i + 3 = n + 1 := rfl
  rw [hn, hn', Nat.factorial_succ n, Nat.cast_mul, pow_succ]
  push_cast
  field_simp
  dsimp [n]
  push_cast
  ring

private lemma kRatio_num_series (x : ℝ) :
    HasSum (fun i : ℕ => (1 / (Nat.factorial (2 * i + 1) : ℝ)) * x ^ (2 * i + 3))
      (x ^ 2 * Real.sinh x) := by
  apply ((Real.hasSum_sinh x).mul_left (x ^ 2)).congr_fun
  intro i
  rw [show 2 * i + 3 = (2 * i + 1) + 2 by omega, pow_add]
  ring

private lemma k_coeff (i : ℕ) :
    1 / (Nat.factorial (2 * i + 1) : ℝ) =
      ((2 * i + 3 : ℕ) : ℝ) * (((2 * i + 2 : ℕ) : ℝ) /
        (Nat.factorial (2 * i + 3) : ℝ)) := by
  let n := 2 * i + 1
  have h1 : 2 * i + 2 = n + 1 := by dsimp [n]
  have h2 : 2 * i + 3 = (n + 1) + 1 := by dsimp [n]
  rw [h1, h2, Nat.factorial_succ (n + 1), Nat.factorial_succ n]
  change 1 / (n.factorial : ℝ) =
    ↑(n + 1 + 1) * (↑(n + 1) / ↑((n + 1 + 1) * ((n + 1) * n.factorial)))
  push_cast
  field_simp

private lemma kRatio_ge_three {x : ℝ} (hx : 0 < x) : 3 ≤ kRatio x := by
  apply (le_div_iff₀ (L_pos hx)).2
  refine ((L_series x).mul_left 3).summable.tsum_le_tsum ?_ (kRatio_num_series x).summable
    |> fun h => by simpa only [((L_series x).mul_left 3).tsum_eq, (kRatio_num_series x).tsum_eq] using h
  intro i
  rw [k_coeff]
  push_cast
  have h : 0 ≤ (2 * (i : ℝ) + 2) / (Nat.factorial (2 * i + 3) : ℝ) *
      x ^ (2 * i + 3) := by positivity
  nlinarith only [mul_nonneg (by positivity : 0 ≤ 2 * (i : ℝ)) h]

private lemma kRatio_mono : MonotoneOn kRatio (Set.Ioi 0) := by
  intro x hx y hy hxy
  apply (div_le_div_iff₀ (L_pos hx) (L_pos hy)).2
  refine series_cross_le (e := fun i => 2 * i + 3) (fun _ _ h => by dsimp; omega) ?_
    (le_of_lt hx) hxy (kRatio_num_series x) (kRatio_num_series y) (L_series x) (L_series y)
  intro i j hij
  rw [k_coeff i, k_coeff j]
  have h : ((2 * i + 3 : ℕ) : ℝ) ≤ ((2 * j + 3 : ℕ) : ℝ) := by exact_mod_cast (show 2 * i + 3 ≤ 2 * j + 3 by omega)
  nlinarith only [mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ (((2 * j + 2 : ℕ) : ℝ) / (Nat.factorial (2 * j + 3) : ℝ)) *
      (((2 * i + 2 : ℕ) : ℝ) / (Nat.factorial (2 * i + 3) : ℝ)) by positivity)]

private lemma two_sinh_sub_le_L {x : ℝ} (hx : 0 < x) :
    2 * (Real.sinh x - x) ≤ L x := by
  have h := ((sinh_tail x).mul_left 2).summable.tsum_le_tsum
    (fun i => by
      rw [← mul_div_assoc, div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      push_cast
      nlinarith only [mul_nonneg (by positivity : 0 ≤ (i : ℝ)) (pow_nonneg hx.le (2 * i + 3))])
    (L_series x).summable
  simpa only [((sinh_tail x).mul_left 2).tsum_eq, (L_series x).tsum_eq] using h

private lemma H_series (s q : ℝ) :
    HasSum (fun i : ℕ => (s ^ (2 * i + 3) - s) / (Nat.factorial (2 * i + 3) : ℝ) *
        q ^ (2 * i + 3)) (H q s) := by
  have hh := (sinh_tail (s * q)).sub ((sinh_tail q).mul_left s)
  have he : Real.sinh (s * q) - s * q - s * (Real.sinh q - q) = H q s := by unfold H; ring
  rw [he] at hh
  refine hh.congr_fun ?_
  intro i
  rw [mul_pow]
  ring

/-! ### The scalar differential equation -/

private def T (x : ℝ) : ℝ := L x / Real.sinh x

private def kSlope (x : ℝ) : ℝ := kRatio x * (3 + T x - kRatio x) / x

private lemma k_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt kRatio (kSlope x) x := by
  convert (((hasDerivAt_id x).pow 2).mul (Real.hasDerivAt_sinh x)).div
    (L_deriv x) (L_pos hx).ne' using 1
  · rfl
  · obtain hs := (Real.sinh_pos_iff.mpr hx).ne'
    have hL := L_pos hx
    simp only [kSlope, T, kRatio, Pi.pow_apply, Pi.mul_apply, id_eq]
    field_simp [hx.ne', hs, hL.ne']
    unfold L
    ring

private lemma kSlope_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ kSlope x := by
  have h := kRatio_mono.derivWithin_nonneg (x := x)
  rwa [derivWithin_of_isOpen isOpen_Ioi hx, (k_deriv hx).deriv] at h

private lemma k_times_T {x : ℝ} (hx : 0 < x) : kRatio x * T x = x ^ 2 := by
  unfold kRatio T
  field_simp [(L_pos hx).ne', (Real.sinh_pos_iff.mpr hx).ne']

private lemma T_le_k {x : ℝ} (hx : 0 < x) : T x ≤ kRatio x - 2 := by
  have hsh := Real.sinh_pos_iff.mpr hx
  have hT : 0 < T x := div_pos (L_pos hx) hsh
  have he : (T x * (T x + 2) - x ^ 2) * Real.sinh x ^ 2 = x ^ 2 - Real.sinh x ^ 2 := by
    unfold T L
    field_simp [hsh.ne']
    linear_combination x ^ 2 * Real.cosh_sq_sub_sinh_sq x
  have hle : x ^ 2 ≤ Real.sinh x ^ 2 :=
    (sq_le_sq₀ hx.le hsh.le).2 (Real.self_le_sinh_iff.mpr hx.le)
  have hh := nonpos_of_mul_nonpos_left (show (T x * (T x + 2) - x ^ 2) *
      Real.sinh x ^ 2 ≤ 0 by rw [he]; linarith) (pow_pos hsh 2)
  apply le_of_mul_le_mul_left (b := T x) _ hT
  nlinarith only [hh, k_times_T hx]

private lemma k_sub_mul_kSlope_le {x : ℝ} (hx : 0 < x) :
    (kRatio x - 2) * kSlope x ≤ x := by
  have hk := kRatio_ge_three hx
  have he : x * kSlope x = kRatio x * (3 + T x - kRatio x) := by
    unfold kSlope
    field_simp [hx.ne']
  have eq : x * ((kRatio x - 2) * kSlope x - x) =
      kRatio x * (kRatio x - 3) * (T x - kRatio x + 2) := by
    calc
      _ = (kRatio x - 2) * (x * kSlope x) - kRatio x * T x := by
        rw [k_times_T hx]
        ring
      _ = _ := by rw [he]; ring
  have h : x * ((kRatio x - 2) * kSlope x - x) ≤ 0 := by
    rw [eq]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [T_le_k hx])
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right h hx)

private def K (z : ℝ) : ℝ := kRatio (Real.sqrt z)
private def K₁ (z : ℝ) : ℝ := (z + 3 * K z - K z ^ 2) / (2 * z)

private lemma K_deriv {z : ℝ} (hz : 0 < z) : HasDerivAt K (K₁ z) z := by
  have hx : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  convert (k_deriv hx).comp z (Real.hasDerivAt_sqrt hz.ne') using 1
  · rfl
  · change (z + 3 * K z - K z ^ 2) / (2 * z) =
      K z * (3 + T (Real.sqrt z) - K z) / Real.sqrt z * (1 / (2 * Real.sqrt z))
    have ht : K z * T (Real.sqrt z) = z :=
      (k_times_T hx).trans (Real.sq_sqrt hz.le)
    calc
      _ = (K z * (3 + T (Real.sqrt z) - K z)) / (2 * z) := by
        apply congrArg (fun u : ℝ => u / (2 * z))
        linear_combination -ht
      _ = _ := by
        field_simp [hz.ne', hx.ne']
        rw [Real.sq_sqrt hz.le]

private lemma K₁_deriv {z : ℝ} (hz : 0 < z) :
    HasDerivAt K₁ ((1 - (2 * K z - 1) * K₁ z) / (2 * z)) z := by
  have hh := ((((hasDerivAt_id z).add ((K_deriv hz).const_mul 3)).sub
    ((K_deriv hz).pow 2)).div ((hasDerivAt_id z).const_mul 2) (by positivity : 2 * z ≠ 0))
  convert hh using 1
  · rfl
  · norm_num only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat,
      Nat.reduceSub, pow_one]
    have he : 2 * z * K₁ z = z + 3 * K z - K z ^ 2 := by
      conv_lhs => unfold K₁
      field_simp [hz.ne']
    rw [← he]
    field_simp [hz.ne']
    ring

private lemma K₁_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ K₁ z := by
  let hmono : MonotoneOn K (Set.Ioi 0) := fun x hx y hy hxy =>
    kRatio_mono (Real.sqrt_pos.2 hx) (Real.sqrt_pos.2 hy) (Real.sqrt_le_sqrt hxy)
  have h := hmono.derivWithin_nonneg (x := z)
  rwa [derivWithin_of_isOpen isOpen_Ioi hz, (K_deriv hz).deriv] at h

private def riccatiGap (z : ℝ) : ℝ := z * ((2 * K z - 1) * K₁ z - 1)

private lemma riccatiGap_deriv {z : ℝ} (hz : 0 < z) :
    HasDerivAt riccatiGap (2 * z * K₁ z ^ 2 - (2 * K z - 3) * riccatiGap z / (2 * z)) z := by
  convert (hasDerivAt_id z).mul
    (((((K_deriv hz).const_mul 2).sub_const 1).mul (K₁_deriv hz)).sub_const 1) using 1
  · rfl
  · simp only [id_eq, one_mul, riccatiGap, Pi.mul_apply]
    field_simp [hz.ne']
    ring

/-- At any negative value of the weighted gap the differential equation
forces a positive derivative. The lower bound −z supplies the endpoint. -/
private lemma riccatiGap_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ riccatiGap z := by
  have hk (u : ℝ) (hu : 0 < u) : 3 ≤ K u := kRatio_ge_three (Real.sqrt_pos.2 hu)
  have hl (u : ℝ) (hu : 0 < u) : -u ≤ riccatiGap u := by
    unfold riccatiGap
    nlinarith only [mul_nonneg hu.le (mul_nonneg
      (show 0 ≤ 2 * K u - 1 by linarith [hk u hu]) (K₁_nonneg hu))]
  by_contra! hn
  let ε := min (z / 2) (-riccatiGap z / 2)
  have hε : 0 < ε := lt_min (by positivity) (by linarith)
  have hεz : ε < z := (min_le_left _ _).trans_lt (by linarith)
  have hεval : riccatiGap z < riccatiGap ε := by
    have ha : ε ≤ -riccatiGap z / 2 := min_le_right _ _
    linarith only [ha, hl ε hε, hn]
  have hc : ContinuousOn riccatiGap (Set.Icc ε z) := fun u hu =>
    (riccatiGap_deriv (hε.trans_le hu.1)).continuousAt.continuousWithinAt
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hεz.le) hc
  have huv : riccatiGap u ≤ riccatiGap z := hmin ⟨hεz.le, le_rfl⟩
  have hεu : ε < u := by
    refine lt_of_le_of_ne hu.1 ?_
    intro he
    subst u
    exact (not_lt_of_ge huv) hεval
  have hg : riccatiGap u < 0 := huv.trans_lt hn
  have hderiv : 0 < 2 * u * K₁ u ^ 2 - (2 * K u - 3) * riccatiGap u / (2 * u) := by
    apply sub_pos.mpr
    exact (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith [hk u (hε.trans hεu)]) hg)
      (mul_pos (by norm_num) (hε.trans hεu))).trans_le
      (mul_nonneg (mul_nonneg (by norm_num) (hε.trans hεu).le) (sq_nonneg _))
  have hfilter : 𝓝[<] u ≤ 𝓝[≠] u :=
    nhdsWithin_mono _ fun _ hv => ne_of_lt hv
  have hpos := ((riccatiGap_deriv (hε.trans hεu)).tendsto_slope.mono_left hfilter).eventually
    (lt_mem_nhds hderiv)
  have ha : ∀ᶠ v in 𝓝[<] u, ε < v := nhdsWithin_le_nhds (lt_mem_nhds hεu)
  have hb : ∀ᶠ v in 𝓝[<] u, v < u := self_mem_nhdsWithin
  have he : ∀ᶠ v in 𝓝[<] u, False := by
    filter_upwards [hpos, ha, hb] with v hv hve hvu
    rw [slope_def_field] at hv
    exact (not_lt_of_ge (div_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (hmin ⟨hve.le, hvu.le.trans hu.2⟩)) (sub_nonpos.mpr hvu.le))) hv
  exact he.exists.choose_spec

private lemma K₁_antitone : AntitoneOn K₁ (Set.Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun z hz => (K₁_deriv hz).continuousAt.continuousWithinAt)
    (fun z hz => (K₁_deriv (by simpa only [interior_Ioi, Set.mem_Ioi] using hz)).differentiableAt.differentiableWithinAt) ?_
  intro z hz
  rw [interior_Ioi] at hz
  rw [(K₁_deriv hz).deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (mul_nonneg (by norm_num) (le_of_lt hz))
  have hh := nonneg_of_mul_nonneg_right (riccatiGap_nonneg hz) (show 0 < z from hz)
  linarith only [hh]

/-! ### A comparison of normalized integrals -/

private def γ (x t : ℝ) : ℝ := L (t * x) / (t ^ 2 * L x)
private def Iγ (x u : ℝ) : ℝ := (Real.sinh x - Real.sinh (u * x) / u) / L x
private def mRatio (x u : ℝ) : ℝ := (Iγ x u)⁻¹

private lemma γ_pos {x t : ℝ} (hx : 0 < x) (ht : 0 < t) : 0 < γ x t :=
  div_pos (L_pos (mul_pos ht hx)) (mul_pos (sq_pos_of_pos ht) (L_pos hx))

private lemma γ_one {x : ℝ} (hx : 0 < x) : γ x 1 = 1 := by simp [γ, (L_pos hx).ne']

private lemma γ_deriv {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    HasDerivAt (γ x) ((kRatio (t * x) - 2) * γ x t / t) t := by
  have htx := L_pos (mul_pos ht hx)
  convert ((L_deriv (t * x)).comp t ((hasDerivAt_id t).mul_const x)).div
      (((hasDerivAt_id t).pow 2).mul_const (L x)) (mul_pos (sq_pos_of_pos ht) (L_pos hx)).ne' using 1
  · rfl
  · simp only [Function.comp_apply, id_eq, one_mul, γ, kRatio, Pi.pow_apply]
    field_simp [ht.ne', htx.ne', (L_pos hx).ne']
    ring

private lemma Iγ_deriv {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    HasDerivAt (Iγ x) (-γ x t) t := by
  convert ((hasDerivAt_const t (Real.sinh x)).sub
    ((((hasDerivAt_id t).mul_const x).sinh).div (hasDerivAt_id t) ht.ne')).div_const (L x) using 1
  · rfl
  · simp only [γ, id_eq, one_mul, mul_one, zero_sub]
    have hnum : Real.cosh (t * x) * x * t - Real.sinh (t * x) = L (t * x) := by
      unfold L
      ring
    rw [hnum]
    field_simp [ht.ne', (L_pos hx).ne']

private lemma γ_integral {x u : ℝ} (hx : 0 < x) (hu : 0 < u) (hu₁ : u ≤ 1) :
    (∫ t in u..1, γ x t) = Iγ x u := by
  have hG : ContinuousOn (γ x) (Set.Icc u 1) := fun t ht =>
    (γ_deriv hx (hu.trans_le ht.1)).continuousAt.continuousWithinAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := -Iγ x) (f' := γ x)
    (fun t ht => by
      rw [uIcc_of_le hu₁] at ht
      simpa only [neg_neg] using (Iγ_deriv hx (hu.trans_le ht.1)).neg)
    (hG.intervalIntegrable_of_Icc hu₁)
  simpa [Iγ] using hh

private lemma Iγ_pos {x u : ℝ} (hx : 0 < x) (hu : 0 < u) (hu₁ : u < 1) :
    0 < Iγ x u := by
  rw [← γ_integral hx hu hu₁.le]
  refine intervalIntegral.integral_pos hu₁
    (fun t ht => (γ_deriv hx (hu.trans_le ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => (γ_pos hx (hu.trans ht.1)).le) ⟨1, ⟨hu₁.le, le_rfl⟩, γ_pos hx one_pos⟩

private lemma mRatio_deriv {x u : ℝ} (hx : 0 < x) (hu : 0 < u) (hu₁ : u < 1) :
    HasDerivAt (mRatio x) (γ x u / (Iγ x u) ^ 2) u := by
  change HasDerivAt ((Iγ x)⁻¹) _ u
  simpa only [neg_neg] using (Iγ_deriv hx hu).inv (Iγ_pos hx hu hu₁).ne'

private lemma γ_over_t_mono {x : ℝ} (hx : 0 < x) :
    MonotoneOn (fun t => γ x t / t) (Set.Ioi 0) := by
  have hD (t : ℝ) (ht : 0 < t) : HasDerivAt (fun t => γ x t / t)
      (((kRatio (t * x) - 2) * γ x t / t * t - γ x t) / t ^ 2) t := by
    simpa only [id_eq, mul_one] using (γ_deriv hx ht).fun_div (hasDerivAt_id t) ht.ne'
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun t ht => (hD t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hD t (by simpa only [interior_Ioi, Set.mem_Ioi] using ht)).differentiableAt.differentiableWithinAt) ?_
  intro t ht
  rw [interior_Ioi] at ht
  rw [(hD t ht).deriv]
  rw [div_mul_cancel₀ _ (ne_of_gt ht)]
  apply div_nonneg _ (sq_nonneg _)
  nlinarith only [mul_nonneg (sub_nonneg.mpr (kRatio_ge_three (mul_pos ht hx))) (γ_pos hx ht).le]

private def ell (x y z : ℝ) : ℝ :=
  Real.log (L (Real.sqrt z * x)) - Real.log (L x) -
    (Real.log (L (Real.sqrt z * y)) - Real.log (L y))

private lemma ell_deriv {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    HasDerivAt (ell x y) ((K (x ^ 2 * z) - K (y ^ 2 * z)) / (2 * z)) z := by
  have hr := Real.sqrt_pos.2 hz
  have hd (v : ℝ) (hv : 0 < v) :
      HasDerivAt (fun z => Real.log (L (Real.sqrt z * v))) (K (v ^ 2 * z) / (2 * z)) z := by
    have hrv := L_pos (mul_pos hr hv)
    have h := (L_deriv (Real.sqrt z * v)).comp z ((Real.hasDerivAt_sqrt hz.ne').mul_const v)
    change HasDerivAt (fun t => L (Real.sqrt t * v)) _ z at h
    have hh := h.log hrv.ne'
    convert hh using 1
    have he : Real.sqrt (v ^ 2 * z) = Real.sqrt z * v := by
      rw [Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq hv.le, mul_comm]
    simp only [K, he, kRatio]
    field_simp [hz.ne', hr.ne', hrv.ne']
    rw [Real.sq_sqrt hz.le]
  convert ((hd x hx).sub_const (Real.log (L x))).sub
    ((hd y hy).sub_const (Real.log (L y))) using 1
  · rfl
  · ring

private lemma ell_deriv_integral {x y z : ℝ} (hy : 0 < y) (hxy : y ≤ x) (hz : 0 < z) :
    (K (x ^ 2 * z) - K (y ^ 2 * z)) / (2 * z) =
      (∫ t in y ^ 2..x ^ 2, K₁ (t * z)) / 2 := by
  have hYX : y ^ 2 ≤ x ^ 2 := (sq_le_sq₀ hy.le (hy.le.trans hxy)).2 hxy
  have hp (t : ℝ) (ht : t ∈ Set.Icc (y ^ 2) (x ^ 2)) : 0 < t * z :=
    mul_pos ((sq_pos_of_pos hy).trans_le ht.1) hz
  have hc : ContinuousOn (fun t => K₁ (t * z)) (Set.Icc (y ^ 2) (x ^ 2)) :=
    fun t ht => by
      have h : ContinuousAt (fun v : ℝ => v * z) t := ((hasDerivAt_id t).mul_const z).continuousAt
      exact ((K₁_deriv (hp t ht)).continuousAt.comp' (f := fun r : ℝ => r * z) h).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => K (t * z)) (f' := fun t => K₁ (t * z) * z)
    (by
      intro t ht
      rw [uIcc_of_le hYX] at ht
      have hK := (K_deriv (hp t ht)).comp (h₂ := K) t ((hasDerivAt_id t).mul_const z)
      change HasDerivAt (K ∘ (fun y : ℝ => id y * z)) _ t
      simpa only [one_mul] using hK)
    ((hc.mul continuousOn_const).intervalIntegrable_of_Icc hYX)
  rw [intervalIntegral.integral_mul_const] at h
  rw [← h]
  exact mul_div_mul_right _ _ hz.ne'

private lemma ell_concave {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) :
    ConcaveOn ℝ (Set.Ioi 0) (ell x y) := by
  have hx := hy.trans_le hxy
  refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0)
    (fun z hz => (ell_deriv hx hy hz).continuousAt.continuousWithinAt)
    (fun z hz => (ell_deriv hx hy (by simpa only [interior_Ioi, Set.mem_Ioi] using hz)).differentiableAt.differentiableWithinAt) ?_
  intro t ht u hu htu
  rw [interior_Ioi] at ht hu
  rw [(ell_deriv hx hy ht).deriv, (ell_deriv hx hy hu).deriv,
    ell_deriv_integral hy hxy ht, ell_deriv_integral hy hxy hu]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hYX : y ^ 2 ≤ x ^ 2 := (sq_le_sq₀ hy.le hx.le).2 hxy
  have hp (v : ℝ) (hv : v ∈ Set.Icc (y ^ 2) (x ^ 2)) : 0 < v :=
    (sq_pos_of_pos hy).trans_le hv.1
  have hc (z : ℝ) (hz : 0 < z) : ContinuousOn (fun v => K₁ (v * z)) (Set.Icc (y ^ 2) (x ^ 2)) :=
    fun v hv => by
      have h : ContinuousAt (fun v : ℝ => v * z) v := ((hasDerivAt_id v).mul_const z).continuousAt
      exact ((K₁_deriv (mul_pos (hp v hv) hz)).continuousAt.comp' (f := fun r : ℝ => r * z) h).continuousWithinAt
  exact intervalIntegral.integral_mono_on hYX ((hc u hu).intervalIntegrable_of_Icc hYX)
    ((hc t ht).intervalIntegrable_of_Icc hYX) fun v hv =>
      K₁_antitone (mul_pos (hp v hv) ht) (mul_pos (hp v hv) hu)
        (mul_le_mul_of_nonneg_left htu (hp v hv).le)

private lemma ell_mono {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) :
    MonotoneOn (ell x y) (Set.Ioi 0) := by
  have hx := hy.trans_le hxy
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun z hz => (ell_deriv hx hy hz).continuousAt.continuousWithinAt)
    (fun z hz => (ell_deriv hx hy (by simpa only [interior_Ioi, Set.mem_Ioi] using hz)).differentiableAt.differentiableWithinAt) ?_
  intro z hz
  rw [interior_Ioi] at hz
  rw [(ell_deriv hx hy hz).deriv, ell_deriv_integral hy hxy hz]
  apply div_nonneg _ (by norm_num)
  have hYX : y ^ 2 ≤ x ^ 2 := (sq_le_sq₀ hy.le hx.le).2 hxy
  exact intervalIntegral.integral_nonneg hYX fun t ht =>
    K₁_nonneg (mul_pos ((sq_pos_of_pos hy).trans_le ht.1) hz)

private lemma exp_ell {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : 0 < t) :
    Real.exp (ell x y (t ^ 2)) = γ x t / γ y t := by
  simp only [ell, Real.sqrt_sq ht.le, Real.exp_sub, Real.exp_log (L_pos hx),
    Real.exp_log (L_pos hy), Real.exp_log (L_pos (mul_pos ht hx)),
    Real.exp_log (L_pos (mul_pos ht hy)), γ]
  field_simp [ht.ne', (L_pos hx).ne', (L_pos hy).ne', (L_pos (mul_pos ht hy)).ne']

/-- With weight γ, the mean of t² on [u,1] is at least its midpoint.
Compare γ(t)/t with its value at the square root of the midpoint. -/
private lemma gamma_second_moment {x u : ℝ} (hx : 0 < x) (hu : 0 < u) (hu₁ : u < 1) :
    0 ≤ ∫ t in u..1, (t ^ 2 - (u ^ 2 + 1) / 2) * γ x t := by
  let m := (u ^ 2 + 1) / 2
  let v := Real.sqrt m
  have hv : 0 < v := Real.sqrt_pos.2 (by dsimp [m]; positivity)
  have hv₂ : v ^ 2 = m := Real.sq_sqrt (by dsimp [m]; positivity)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc u 1) :
      (γ x v / v) * (t * (t ^ 2 - m)) ≤ (t ^ 2 - m) * γ x t := by
    have ht₀ := hu.trans_le ht.1
    rcases le_total v t with h | h
    · have hg := γ_over_t_mono hx hv ht₀ h
      rw [le_div_iff₀ ht₀] at hg
      have hm : 0 ≤ t ^ 2 - m := by rw [← hv₂]; exact sub_nonneg.mpr ((sq_le_sq₀ hv.le ht₀.le).2 h)
      have hh := mul_le_mul_of_nonneg_left hg hm
      nlinarith only [hh]
    · have hg := γ_over_t_mono hx ht₀ hv h
      rw [div_le_iff₀ ht₀] at hg
      have hm : t ^ 2 - m ≤ 0 := by rw [← hv₂]; exact sub_nonpos.mpr ((sq_le_sq₀ ht₀.le hv.le).2 h)
      have hh := mul_le_mul_of_nonpos_left hg hm
      nlinarith only [hh]
  have hval : (∫ t in u..1, t * (t ^ 2 - m)) = 0 := by
    have hF (t : ℝ) : HasDerivAt (fun t => (t ^ 2 - m) ^ 2 / 4) (t * (t ^ 2 - m)) t := by
      convert ((((hasDerivAt_id t).pow 2).sub_const m).pow 2).div_const 4 using 1
      · rfl
      · simp only [id_eq, mul_one, Pi.pow_apply]
        ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
      ((show Continuous (fun t : ℝ => t * (t ^ 2 - m)) by fun_prop).intervalIntegrable (μ := volume) u 1)]
    dsimp [m]
    ring
  have hc : ContinuousOn (γ x) (Set.Icc u 1) := fun t ht =>
    (γ_deriv hx (hu.trans_le ht.1)).continuousAt.continuousWithinAt
  have hR : ContinuousOn (fun t => (t ^ 2 - m) * γ x t) (Set.Icc u 1) :=
    (show Continuous (fun t : ℝ => t ^ 2 - m) by fun_prop).continuousOn.mul hc
  have h := intervalIntegral.integral_mono_on hu₁.le
    ((show Continuous (fun t : ℝ => γ x v / v * (t * (t ^ 2 - m))) by fun_prop).intervalIntegrable (μ := volume) u 1)
    (hR.intervalIntegrable_of_Icc hu₁.le) hpoint
  simpa only [intervalIntegral.integral_const_mul, hval, mul_zero] using h

/-- Integrate the chord bound for ell, followed by the tangent bound for exp. -/
private lemma Iγ_jensen {x y u : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hu : 0 < u) (hu₁ : u < 1) :
    Real.exp (ell x y (u ^ 2) / 2) * Iγ y u ≤ Iγ x u := by
  let m := (u ^ 2 + 1) / 2
  let e := ell x y (u ^ 2)
  let ℓSlope := -e / (1 - u ^ 2)
  let E := Real.exp (e / 2)
  have hx := hy.trans_le hyx
  have hu₀ : 0 < u ^ 2 := sq_pos_of_pos hu
  have hu₂ : u ^ 2 < 1 := by nlinarith only [mul_pos (sub_pos.mpr hu₁) (show 0 < 1 + u by positivity)]
  have hℓ : ell x y 1 = 0 := by simp [ell]
  have he : e ≤ 0 := by
    change ell x y (u ^ 2) ≤ 0
    rw [← hℓ]
    exact ell_mono hy hyx (show u ^ 2 ∈ Set.Ioi 0 from hu₀)
      (show (1 : ℝ) ∈ Set.Ioi 0 by exact Set.mem_Ioi.mpr Real.zero_lt_one) hu₂.le
  have hℓSlope : 0 ≤ ℓSlope := div_nonneg (neg_nonneg.mpr he) (sub_pos.mpr hu₂).le
  have hE : 0 < E := Real.exp_pos _
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc u 1) :
      E * γ y t + (E * ℓSlope) * ((t ^ 2 - m) * γ y t) ≤ γ x t := by
    have ht₀ := hu.trans_le ht.1
    let α := (1 - t ^ 2) / (1 - u ^ 2)
    let β := (t ^ 2 - u ^ 2) / (1 - u ^ 2)
    have hα : 0 ≤ α := div_nonneg
      (sub_nonneg.mpr (by simpa only [one_pow] using (sq_le_sq₀ ht₀.le zero_le_one).2 ht.2))
      (sub_nonneg.mpr hu₂.le)
    have hβ : 0 ≤ β := div_nonneg (sub_nonneg.mpr ((sq_le_sq₀ hu.le ht₀.le).2 ht.1)) (by linarith)
    have hsum : α + β = 1 := by dsimp [α, β]; field_simp [ne_of_gt (sub_pos.mpr hu₂)]; ring
    have ht₂ : α * u ^ 2 + β * 1 = t ^ 2 := by
      dsimp [α, β]
      field_simp [ne_of_gt (sub_pos.mpr hu₂)]
      ring
    have hchord := (ell_concave hy hyx).2 (show u ^ 2 ∈ Set.Ioi 0 from hu₀)
      (show (1 : ℝ) ∈ Set.Ioi 0 by exact Set.mem_Ioi.mpr Real.zero_lt_one) hα hβ hsum
    simp only [smul_eq_mul] at hchord
    rw [ht₂, hℓ, mul_zero, add_zero] at hchord
    have hac : α * e = e / 2 + ℓSlope * (t ^ 2 - m) := by
      dsimp [α, ℓSlope, m]
      field_simp [ne_of_gt (sub_pos.mpr hu₂)]
      ring
    have htang := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (ℓSlope * (t ^ 2 - m))) hE.le
    have hmajor : E * Real.exp (ℓSlope * (t ^ 2 - m)) ≤ γ x t / γ y t := by
      rw [← exp_ell hx hy ht₀, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (hac ▸ hchord)
    have hbound := (le_div_iff₀ (γ_pos hy ht₀)).1 (htang.trans hmajor)
    nlinarith only [hbound]
  have hc (v : ℝ) (hv : 0 < v) : ContinuousOn (γ v) (Set.Icc u 1) := fun t ht =>
    (γ_deriv hv (hu.trans_le ht.1)).continuousAt.continuousWithinAt
  have hL : IntervalIntegrable (fun t => E * γ y t) volume u 1 :=
    ((hc y hy).const_mul E).intervalIntegrable_of_Icc hu₁.le
  have hC : ContinuousOn (fun t => (t ^ 2 - m) * γ y t) (Set.Icc u 1) :=
    (show Continuous (fun t : ℝ => t ^ 2 - m) by fun_prop).continuousOn.mul (hc y hy)
  have hR : IntervalIntegrable (fun t => (E * ℓSlope) * ((t ^ 2 - m) * γ y t)) volume u 1 :=
    (hC.const_mul (E * ℓSlope)).intervalIntegrable_of_Icc hu₁.le
  have h := intervalIntegral.integral_mono_on hu₁.le (hL.add hR)
    ((hc x hx).intervalIntegrable_of_Icc hu₁.le) hpoint
  rw [intervalIntegral.integral_add hL hR, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, γ_integral hy hu hu₁.le, γ_integral hx hu hu₁.le] at h
  exact (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hE.le hℓSlope)
    (gamma_second_moment hy hu hu₁))).trans h

private lemma mRatio_slope_le {x y u : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hu : 0 < u) (hu₁ : u < 1) :
    γ x u / Iγ x u ^ 2 ≤ γ y u / Iγ y u ^ 2 := by
  have hx := hy.trans_le hyx
  have hp := Iγ_jensen hy hyx hu hu₁
  have hh := (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le (Iγ_pos hy hu hu₁).le)
    (Iγ_pos hx hu hu₁).le).2 hp
  have he : Real.exp (ell x y (u ^ 2) / 2) ^ 2 = Real.exp (ell x y (u ^ 2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, he, exp_ell hx hy hu] at hh
  rw [div_mul_eq_mul_div, div_le_iff₀ (γ_pos hy hu)] at hh
  exact (div_le_div_iff₀ (sq_pos_of_pos (Iγ_pos hx hu hu₁)) (sq_pos_of_pos (Iγ_pos hy hu hu₁))).2
    (by simpa only [mul_comm (Iγ x u ^ 2) (γ y u)] using hh)

private lemma mRatio_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (fun u => mRatio x u - 1 / (1 - u)) (𝓝[<] (1 : ℝ)) (𝓝 ((kRatio x - 2) / 2)) := by
  let F (u : ℝ) := 1 - u - Iγ x u
  let G (u : ℝ) := (u - 1) ^ 2
  have hγ := γ_deriv hx one_pos
  rw [γ_one hx, one_mul, div_one, mul_one] at hγ
  have hI1 : Iγ x 1 = 0 := by simp [Iγ]
  have hF (u : ℝ) (hu : 0 < u) : HasDerivAt F (γ x u - 1) u := by
    convert ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).sub (Iγ_deriv hx hu) using 1
    · rfl
    · ring
  have hG (u : ℝ) : HasDerivAt G (2 * (u - 1)) u := by
    convert ((hasDerivAt_id u).sub_const 1).pow 2 using 1
    · rfl
    · simp [id_eq]
  have hflt : 𝓝[<] (1 : ℝ) ≤ 𝓝[≠] (1 : ℝ) :=
    nhdsWithin_mono _ fun _ hv => ne_of_lt hv
  have h₁ : ∀ᶠ u in 𝓝[<] (1 : ℝ), 0 < u :=
    nhdsWithin_le_nhds (lt_mem_nhds one_pos)
  have h₂ : ∀ᶠ u in 𝓝[<] (1 : ℝ), u < 1 := self_mem_nhdsWithin
  have htA : Tendsto (fun u => (γ x u - 1) / (2 * (u - 1)))
      (𝓝[<] (1 : ℝ)) (𝓝 ((kRatio x - 2) / 2)) := by
    apply ((hγ.tendsto_slope.mono_left hflt).div_const 2).congr'
    filter_upwards with u
    rw [slope_def_field, γ_one hx, div_div, mul_comm (u - 1) 2]
  have hFA : Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    simpa [F, hI1] using ((hF 1 one_pos).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1))
  have hGA : Tendsto G (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    simpa [G] using ((hG 1).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1))
  have htL := HasDerivAt.lhopital_zero_nhdsLT (h₁.mono hF) (Eventually.of_forall hG)
    (h₂.mono fun u hu => mul_ne_zero (by norm_num) (sub_ne_zero.mpr hu.ne)) hFA hGA htA
  have htR : Tendsto (fun u => Iγ x u / (1 - u)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have h := Iγ_deriv hx one_pos
    rw [γ_one hx] at h
    apply (by
      simpa only [neg_neg] using (h.tendsto_slope.mono_left hflt).neg :
        Tendsto (fun u => -slope (Iγ x) 1 u) (𝓝[<] (1 : ℝ)) (𝓝 1)).congr'
    filter_upwards with u
    rw [slope_def_field, hI1, sub_zero, ← neg_div,
      show 1 - u = -(u - 1) by ring, div_neg, neg_div]
  have h := htL.div htR one_ne_zero
  rw [div_one] at h
  apply h.congr'
  filter_upwards [h₁, h₂] with u hu hlt
  dsimp [F, G, mRatio]
  field_simp [(Iγ_pos hx hu hlt).ne', sub_ne_zero.mpr hlt.ne, sub_ne_zero.mpr hlt.ne']
  ring

private lemma mRatio_gap {x y u : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hu : 0 < u) (hu₁ : u < 1) :
    (kRatio x - kRatio y) / 2 ≤ mRatio x u - mRatio y u := by
  have hx := hy.trans_le hyx
  let f (v : ℝ) := mRatio x v - mRatio y v
  have hd (v : ℝ) (hv : v ∈ Set.Ioo (0 : ℝ) 1) :
      HasDerivAt f (γ x v / Iγ x v ^ 2 - γ y v / Iγ y v ^ 2) v :=
    (mRatio_deriv hx hv.1 hv.2).sub (mRatio_deriv hy hv.1 hv.2)
  have hm : AntitoneOn f (Set.Ioo 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo ..)
      (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
      (fun v hv => (hd v (by simpa only [interior_Ioo] using hv)).differentiableAt.differentiableWithinAt) ?_
    intro v hv
    rw [interior_Ioo] at hv
    rw [(hd v hv).deriv]
    exact sub_nonpos.mpr (mRatio_slope_le hy hyx hv.1 hv.2)
  have he : (kRatio x - 2) / 2 - (kRatio y - 2) / 2 = (kRatio x - kRatio y) / 2 := by ring
  have ht := (mRatio_limit hx).sub (mRatio_limit hy)
  rw [he] at ht
  have hf : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 ((kRatio x - kRatio y) / 2)) := by
    apply ht.congr'
    filter_upwards with v
    dsimp [f]
    ring
  apply le_of_tendsto hf
  have ht₁ : ∀ᶠ v in 𝓝[<] (1 : ℝ), u < v := nhdsWithin_le_nhds (lt_mem_nhds hu₁)
  have ht₂ : ∀ᶠ v in 𝓝[<] (1 : ℝ), v < 1 := self_mem_nhdsWithin
  filter_upwards [ht₁, ht₂] with v hv hv'
  exact hm ⟨hu, hu₁⟩ ⟨hu.trans hv, hv'⟩ hv.le

private lemma mRatio_ge_two {x u : ℝ} (hx : 0 < x) (hu : 0 < u) (hu₁ : u < 1) :
    2 ≤ mRatio x u := by
  have hh := Iγ_pos hx hu hu₁
  have hg := Real.self_le_sinh_iff.mpr (mul_pos hu hx).le
  have hm : x ≤ Real.sinh (u * x) / u := (le_div_iff₀ hu).2 (by simpa only [mul_comm x u] using hg)
  rw [mRatio, ← one_div]
  apply (le_div_iff₀ hh).2
  unfold Iγ
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (L_pos hx)).2
  linarith only [two_sinh_sub_le_L hx, hm]

private lemma mRatio_ge_T {x u : ℝ} (hx : 0 < x) (hu : 0 < u) (hu₁ : u < 1) :
    T x ≤ mRatio x u := by
  have hh := Iγ_pos hx hu hu₁
  have hg := Real.sinh_pos_iff.mpr (mul_pos hu hx)
  have hs := Real.sinh_pos_iff.mpr hx
  rw [T, mRatio, ← one_div]
  apply (div_le_div_iff₀ hs hh).2
  unfold Iγ
  rw [mul_div_cancel₀ _ (L_pos hx).ne', one_mul]
  exact sub_le_self _ (div_nonneg hg.le hu.le)

private lemma normalize_p_A {q s : ℝ} (hq : 0 < q) (hs : 1 < s) :
    p q s = (mRatio (s * q) (1 / s) + 1) / s ∧
    A₂ q s = kRatio (s * q) * mRatio (s * q) (1 / s) / s ^ 2 := by
  have hs₀ : 0 < s := by linarith
  have hL := L_pos (mul_pos hs₀ hq)
  have hH := H_pos hq hs
  have he : Iγ (s * q) (1 / s) = H q s / L (s * q) := by
    unfold Iγ H
    rw [show 1 / s * (s * q) = q by field_simp [hs₀.ne']]
    field_simp [hs₀.ne']
  rw [mRatio, he, inv_div]
  constructor
  · unfold p h₁
    field_simp [hs₀.ne', hH.ne']
    unfold L H
    ring_nf
  · unfold A₂ h₂ kRatio
    rw [div_mul_div_comm, mul_comm (L (s * q)) (H q s), mul_div_mul_right _ _ hL.ne']
    field_simp [hs₀.ne', hH.ne']

/-- The lower bound on D and the upper bound on D' from the normalized
integrals. Here `p₁` is the derivative of `p` with respect to s. -/
private lemma p_halfDiff_bounds {a b s : ℝ} (hb : 0 < b) (hba : b ≤ a) (hs : 1 < s) :
    0 ≤ halfDiff (p a s) (p b s) ∧
    halfDiff (p₁ a s) (p₁ b s) ≤ avg a b * halfDiff a b / 2 := by
  have ha := hb.trans_le hba
  have hs₀ : 0 < s := by linarith
  let x := s * a
  let y := s * b
  let u := 1 / s
  have hy : 0 < y := mul_pos hs₀ hb
  have hxy : y ≤ x := mul_le_mul_of_nonneg_left hba hs₀.le
  have hx := hy.trans_le hxy
  have hu : 0 < u := one_div_pos.mpr hs₀
  have hu₁ : u < 1 := (div_lt_iff₀ hs₀).2 (by simpa only [one_mul] using hs)
  let e := halfDiff (kRatio x) (kRatio y)
  let k₀ := avg (kRatio x) (kRatio y)
  let m₀ := avg (mRatio x u) (mRatio y u)
  let W := halfDiff (mRatio x u) (mRatio y u)
  have he : 0 ≤ e := div_nonneg
    (sub_nonneg.mpr (show kRatio y ≤ kRatio x from kRatio_mono hy hx hxy)) (by norm_num)
  have hW : e / 2 ≤ W := by dsimp [e, W, halfDiff]; linarith only [mRatio_gap hy hxy hu hu₁]
  have hW₀ : 0 ≤ W := by linarith
  have hMk (z : ℝ) (hz : 0 < z) : 2 * mRatio z u ≥ kRatio z - 2 := by
    have hg : 0 ≤ kRatio z * (3 + T z - kRatio z) / z := kSlope_nonneg hz
    have hk : 0 < kRatio z := (by norm_num : 0 < (3 : ℝ)).trans_le (kRatio_ge_three hz)
    have h' := (le_div_iff₀ hz).1 hg
    rw [zero_mul] at h'
    have h := nonneg_of_mul_nonneg_right h' hk
    linarith only [mRatio_ge_two hz hu hu₁, mRatio_ge_T hz hu hu₁, h]
  have heM : k₀ - 2 - 2 * m₀ ≤ 0 := by dsimp [k₀, m₀, avg]; linarith only [hMk x hx, hMk y hy]
  have hpa := normalize_p_A ha hs
  have hpb := normalize_p_A hb hs
  change p a s = (mRatio x u + 1) / s ∧ A₂ a s = kRatio x * mRatio x u / s ^ 2 at hpa
  change p b s = (mRatio y u + 1) / s ∧ A₂ b s = kRatio y * mRatio y u / s ^ 2 at hpb
  have hdiff : halfDiff (p a s) (p b s) = W / s := by
    rw [hpa.1, hpb.1]
    dsimp [W, halfDiff]
    ring
  constructor
  · rw [hdiff]
    exact div_nonneg hW₀ hs₀.le
  apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hs₀)).mp
  have hdiff' : s ^ 2 * halfDiff (p₁ a s) (p₁ b s) =
      e * m₀ + (k₀ - 2 - 2 * m₀) * W := by
    unfold p₁
    rw [hpa.1, hpb.1, hpa.2, hpb.2]
    dsimp [halfDiff, W, e, k₀, m₀, avg]
    field_simp [hs₀.ne']
    ring
  have hex : e * m₀ + (k₀ - 2 - 2 * m₀) * W ≤ (k₀ - 2) * e / 2 := by
    have hh := mul_le_mul_of_nonpos_left hW heM
    nlinarith only [hh]
  have hdif_mono : MonotoneOn (fun z => z ^ 2 - (kRatio z - 2) ^ 2) (Set.Ioi 0) := by
    have hd (z : ℝ) (hz : 0 < z) :
        HasDerivAt (fun z => z ^ 2 - (kRatio z - 2) ^ 2)
          (2 * z - 2 * (kRatio z - 2) * kSlope z) z := by
      have h := ((hasDerivAt_id z).pow 2).sub (((k_deriv hz).sub_const 2).pow 2)
      change HasDerivAt (id ^ 2 - (fun x => kRatio x - 2) ^ 2) _ z
      simpa only [id_eq, mul_one, Nat.cast_ofNat, Nat.reduceSub, pow_one] using h
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hd z (by simpa only [interior_Ioi, Set.mem_Ioi] using hz)).differentiableAt.differentiableWithinAt) ?_
    intro z hz
    rw [interior_Ioi] at hz
    rw [(hd z hz).deriv]
    nlinarith only [k_sub_mul_kSlope_le hz]
  have hxlim : (k₀ - 2) * e / 2 ≤ (x ^ 2 - y ^ 2) / 8 := by
    have hh : y ^ 2 - (kRatio y - 2) ^ 2 ≤ x ^ 2 - (kRatio x - 2) ^ 2 := hdif_mono hy hx hxy
    dsimp [k₀, e, halfDiff, avg]
    nlinarith only [hh]
  rw [hdiff']
  exact hex.trans (hxlim.trans_eq (by dsimp [x, y, avg, halfDiff]; ring))

/-! ### The two remainder terms -/

private lemma w_formula (q s : ℝ) :
    w q s = q * (Real.sinh q - q * Real.exp (-(s * q))) / H q s := by
  unfold w A₂ p h₁ h₂
  rw [← Real.cosh_sub_sinh]
  ring

private lemma j_formula (q s : ℝ) :
    j q s = q ^ 3 * Real.exp (-(s * q)) / H q s := by
  unfold j A₂ A₃ h₂ h₃
  rw [← Real.cosh_sub_sinh]
  ring

private lemma w_pos {q s : ℝ} (hq : 0 < q) (hs : 1 ≤ s) (hs' : 1 < s) :
    0 < w q s := by
  rw [w_formula]
  apply div_pos (mul_pos hq _) (H_pos hq hs')
  apply sub_pos.mpr
  exact (mul_lt_of_lt_one_right hq (Real.exp_lt_one_iff.mpr (by nlinarith))).trans_le
    (Real.self_le_sinh_iff.mpr hq.le)

private lemma p_gt_q {q s : ℝ} (hq : 0 < q) (hs : 1 < s) : q < p q s := by
  have hd (t : ℝ) : HasDerivAt (fun t => h₁ q t - q * H q t)
      (q * (Real.sinh q - q * Real.exp (-(t * q)))) t := by
    have hh := (h₁_deriv q t).sub ((H_deriv_s q t).const_mul q)
    convert hh using 1
    change _ = h₂ q t - q * h₁ q t
    unfold h₂ h₁
    rw [← Real.cosh_sub_sinh]
    ring
  have hm : MonotoneOn (fun t => h₁ q t - q * H q t) (Set.Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1) (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [(hd t).deriv]
    have ht' : 1 ≤ t := le_of_lt (by simpa using ht)
    have hex : Real.exp (-(t * q)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact mul_nonneg hq.le (sub_nonneg.mpr
      ((mul_le_of_le_one_right hq.le hex).trans (Real.self_le_sinh_iff.mpr hq.le)))
  have h0 : 0 < h₁ q 1 - q * H q 1 := by simpa [h₁, H, L] using L_pos hq
  unfold p
  exact (lt_div_iff₀ (H_pos hq hs)).2 (sub_pos.mp (h0.trans_le (hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs.le) hs.le)))

private lemma H_div_cube_mono {s : ℝ} (hs : 1 < s) :
    MonotoneOn (fun q => H q s / q ^ 3) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hseries (q : ℝ) (hq : 0 < q) :
      HasSum (fun i : ℕ => (s ^ (2 * i + 3) - s) / (Nat.factorial (2 * i + 3) : ℝ) *
        q ^ (2 * i)) (H q s / q ^ 3) := by
    refine ((H_series s q).div_const (q ^ 3)).congr_fun ?_
    intro i
    rw [show (2 * i + 3) = 2 * i + 3 by rfl, pow_add q (2 * i) 3, ← mul_assoc,
      mul_div_cancel_right₀ _ (pow_ne_zero _ hq.ne')]
  have hm := (hseries x hx).summable.tsum_le_tsum
    (fun i => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hx) hxy _)
      (div_nonneg (sub_nonneg.mpr (by
        simpa only [pow_one] using pow_le_pow_right₀ hs.le (show 1 ≤ 2 * i + 3 by omega)))
        (by positivity))) (hseries y hy).summable
  simpa only [(hseries x hx).tsum_eq, (hseries y hy).tsum_eq] using hm

private lemma j_antitone {s : ℝ} (hs : 1 < s) : AntitoneOn (fun q => j q s) (Set.Ioi 0) := by
  intro x hx y hy hxy
  change j y s ≤ j x s
  rw [j_formula, j_formula,
    show y ^ 3 * Real.exp (-(s * y)) / H y s = Real.exp (-(s * y)) / (H y s / y ^ 3) by rw [div_div_eq_mul_div]; ring,
    show x ^ 3 * Real.exp (-(s * x)) / H x s = Real.exp (-(s * x)) / (H x s / x ^ 3) by rw [div_div_eq_mul_div]; ring]
  calc
    _ ≤ Real.exp (-(s * x)) / (H y s / y ^ 3) :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith))
        (div_nonneg (H_pos hy hs).le (pow_nonneg (le_of_lt hy) _))
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le
      (div_pos (H_pos hx hs) (pow_pos hx _)) (H_div_cube_mono hs hx hy hxy)

/-- The complete homogeneous polynomial in the two coordinates x and y. -/
private def hseq (x y : ℝ) (m : ℕ) : ℝ :=
  (x ^ (m + 1) - y ^ (m + 1)) / (x - y)

private lemma hseq_pos {x y : ℝ} (hy : 0 < y) (hxy : y < x) (m : ℕ) :
    0 < hseq x y m := by
  exact div_pos (sub_pos.mpr (pow_lt_pow_left₀ hxy hy.le (by omega))) (sub_pos.mpr hxy)

private lemma hseq_zero {x y : ℝ} (hxy : y < x) : hseq x y 0 = 1 := by
  simp [hseq, (sub_pos.mpr hxy).ne']

private lemma hseq_one {x y : ℝ} (hxy : y < x) (h : x + y = 1) : hseq x y 1 = 1 := by
  unfold hseq
  norm_num
  apply (div_eq_one_iff_eq (sub_pos.mpr hxy).ne').2
  linear_combination (x - y) * h

private lemma hseq_recur {x y : ℝ} (hxy : y < x) (hsum : x + y = 1) (m : ℕ) :
    hseq x y (m + 2) = hseq x y (m + 1) - x * y * hseq x y m := by
  unfold hseq
  field_simp [(sub_pos.mpr hxy).ne']
  rw [show m + 2 + 1 = (m + 1) + 2 by omega, show m + 1 + 1 = (m + 1) + 1 by omega]
  simp only [pow_add, pow_one]
  linear_combination (x ^ (m + 1) * x - y ^ (m + 1) * y) * hsum

private lemma hseq_logConcave {x y : ℝ} (hy : 0 < y) (hxy : y < x) (m : ℕ) :
    hseq x y m * hseq x y (m + 2) ≤ hseq x y (m + 1) ^ 2 := by
  have h :
      hseq x y (m + 1) ^ 2 - hseq x y m * hseq x y (m + 2) =
        (x * y) ^ (m + 1) := by
    unfold hseq
    field_simp [(sub_pos.mpr hxy).ne']
    rw [show m + 2 + 1 = (m + 1) + 2 by omega, mul_pow]
    simp only [pow_add, pow_one]
    ring
  exact sub_nonneg.mp (h ▸ pow_nonneg (mul_nonneg (hy.trans hxy).le hy.le) _)

private lemma hseq_antitone {x y : ℝ} (hy : 0 < y) (hxy : y < x) (hsum : x + y = 1) :
    Antitone (hseq x y) := by
  apply antitone_nat_of_succ_le
  intro m
  cases m with
  | zero => rw [hseq_one hxy hsum, hseq_zero hxy]
  | succ m =>
    rw [show m.succ + 1 = m + 2 by omega, hseq_recur hxy hsum]
    exact sub_le_self _ (mul_nonneg (mul_nonneg (hy.trans hxy).le hy.le) (hseq_pos hy hxy m).le)

private lemma hseq_gap {x y : ℝ} (hxy : y < x) (hsum : x + y = 1) (m : ℕ) :
    1 - hseq x y (m + 1) = x * y * (∑ i ∈ range m, hseq x y i) := by
  induction m with
  | zero => simp [hseq_one hxy hsum]
  | succ m ih =>
    rw [show m.succ + 1 = m + 2 by omega, hseq_recur hxy hsum, sum_range_succ]
    linear_combination ih

private lemma hseq_mean_mono {x y : ℝ} (hy : 0 < y) (hxy : y < x) (hsum : x + y = 1) :
    Monotone (fun m : ℕ => (∑ i ∈ range m, hseq x y i) / ((m + 2 : ℕ) * hseq x y m)) := by
  let h := hseq x y
  let P (m : ℕ) := ∑ i ∈ range m, h i
  have hp (m : ℕ) : 0 < h m := hseq_pos hy hxy m
  have hm := hseq_antitone hy hxy hsum
  have hquot : Antitone (fun m => h (m + 1) / h m) := by
    apply antitone_nat_of_succ_le
    intro m
    exact (div_le_div_iff₀ (hp (m + 1)) (hp m)).2 (by
      simpa only [pow_two, mul_comm] using hseq_logConcave hy hxy m)
  change Monotone (fun m : ℕ => P m / ((m + 2 : ℕ) * h m))
  apply monotone_nat_of_le_succ
  intro m
  have h1 : P m * h (m + 1) ≤ (P (m + 1) - h 0) * h m := by
    rw [show P (m + 1) - h 0 = ∑ i ∈ range m, h (i + 1) by
      dsimp [P]; rw [sum_range_succ']; ring, sum_mul, sum_mul]
    apply sum_le_sum
    intro i hi
    have hh := hquot (Nat.le_of_lt (mem_range.mp hi))
    exact (mul_comm (h i) _ ▸ (div_le_div_iff₀ (hp m) (hp i)).1 hh)
  have h2 : P m ≤ (m : ℝ) * h 0 := by
    calc
      _ ≤ ∑ i ∈ range m, h 0 := sum_le_sum fun i _ => hm (Nat.zero_le i)
      _ = _ := by simp [nsmul_eq_mul]
  have h3 : P m * h (m + 1) ≤ (m : ℝ) * h 0 * h m :=
    mul_le_mul h2 (hm (Nat.le_succ m)) (hp _).le (mul_nonneg (Nat.cast_nonneg _) (hp _).le)
  have h4 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ (m : ℝ) + 2 by positivity)
  have h5 : 0 ≤ 2 * h 0 * h m := mul_nonneg (mul_nonneg (by norm_num) (hp _).le) (hp _).le
  apply (div_le_div_iff₀ (mul_pos (by positivity) (hp _)) (mul_pos (by positivity) (hp _))).2
  push_cast
  nlinarith only [h3, h4, h5]

private def wNum (s : ℝ) (n : ℕ) : ℝ :=
  ((s + 1) ^ (n + 2) - (s - 1) ^ (n + 2)) / (Nat.factorial (n + 2) : ℝ)
private def wDen (s : ℝ) (n : ℕ) : ℝ :=
  ((2 * s) ^ (n + 3) - s * ((s + 1) ^ (n + 3) - (s - 1) ^ (n + 3))) /
    (Nat.factorial (n + 3) : ℝ)

private lemma exp_series (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

private lemma w_series_num (s q : ℝ) :
    HasSum (fun i : ℕ => wNum s i * q ^ (i + 3))
      (q * (Real.exp ((s + 1) * q) - Real.exp ((s - 1) * q) - 2 * q)) := by
  let f (i : ℕ) := ((s + 1) * q) ^ i / (i.factorial : ℝ) -
    ((s - 1) * q) ^ i / (i.factorial : ℝ)
  have h : HasSum f (Real.exp ((s + 1) * q) - Real.exp ((s - 1) * q)) :=
    (exp_series ((s + 1) * q)).sub
      (exp_series ((s - 1) * q))
  have h₀ : ∑ i ∈ range 2, f i = 2 * q := by
    norm_num [f, sum_range_succ]
    ring
  have ht := hasSum_drop f 2 _ h
  rw [h₀] at ht
  apply (ht.mul_left q).congr_fun
  intro i
  dsimp only [wNum, f]
  rw [mul_pow (s + 1) q, mul_pow (s - 1) q, pow_succ q (i + 2)]
  ring

private lemma w_series_den (s q : ℝ) :
    HasSum (fun i : ℕ => wDen s i * q ^ (i + 3))
      (Real.exp (2 * s * q) - 1 - s * (Real.exp ((s + 1) * q) - Real.exp ((s - 1) * q))) := by
  let f (i : ℕ) := (2 * s * q) ^ i / (i.factorial : ℝ) -
    s * (((s + 1) * q) ^ i / (i.factorial : ℝ) - ((s - 1) * q) ^ i / (i.factorial : ℝ))
  let d := Real.exp (2 * s * q) - s * (Real.exp ((s + 1) * q) - Real.exp ((s - 1) * q))
  have h : HasSum f d := (exp_series (2 * s * q)).sub
    (((exp_series ((s + 1) * q)).sub
      (exp_series ((s - 1) * q))).mul_left s)
  have h₀ : ∑ i ∈ range 3, f i = 1 := by
    norm_num [f, sum_range_succ]
    ring
  have ht := hasSum_drop f 3 d h
  rw [h₀, show d - 1 = Real.exp (2 * s * q) - 1 -
    s * (Real.exp ((s + 1) * q) - Real.exp ((s - 1) * q)) by dsimp [d]; ring] at ht
  apply ht.congr_fun
  intro i
  dsimp only [wDen, f]
  rw [mul_pow (2 * s) q, mul_pow (s + 1) q, mul_pow (s - 1) q]
  ring

private lemma w_ratio (s q : ℝ) :
    w q s =
      (q * (Real.exp ((s + 1) * q) - Real.exp ((s - 1) * q) - 2 * q)) /
      (Real.exp (2 * s * q) - 1 - s * (Real.exp ((s + 1) * q) - Real.exp ((s - 1) * q))) := by
  have he1 : Real.exp ((s + 1) * q) - Real.exp ((s - 1) * q) =
      2 * Real.exp (s * q) * Real.sinh q := by
    rw [show (s + 1) * q = s * q + q by ring, show (s - 1) * q = s * q + -q by ring,
      Real.exp_add, Real.exp_add, Real.sinh_eq]
    ring
  have he2 : Real.exp (2 * s * q) - 1 = 2 * Real.exp (s * q) * Real.sinh (s * q) := by
    rw [show 2 * s * q = s * q + s * q by ring, Real.exp_add, Real.sinh_eq, Real.exp_neg]
    field_simp [(Real.exp_pos (s * q)).ne']
  rw [w_formula, he1, he2]
  unfold H
  rw [Real.exp_neg]
  field_simp [(Real.exp_pos (s * q)).ne']

private lemma w_coefficients {s : ℝ} (hs : 1 < s) :
    (∀ i, 0 < wDen s i) ∧ Antitone (fun i => wNum s i / wDen s i) := by
  let x := (s + 1) / (2 * s)
  let y := (s - 1) / (2 * s)
  have hs₀ : 0 < s := by linarith
  have hys : 0 < y := div_pos (by linarith) (by positivity)
  have hsub : x - y = 1 / s := by
    dsimp [x, y]
    field_simp [hs₀.ne']
    ring
  have hxy : y < x := sub_pos.mp (hsub ▸ one_div_pos.mpr hs₀)
  have hsum : x + y = 1 := by dsimp [x, y]; field_simp [hs₀.ne']; ring
  have hScale (n : ℕ) :
      (s + 1) ^ (n + 1) - (s - 1) ^ (n + 1) =
      (2 * s) ^ (n + 1) * (hseq x y n / s) := by
    have hX : s + 1 = (2 * s) * x := by dsimp [x]; field_simp [hs₀.ne']
    have hY : s - 1 = (2 * s) * y := by dsimp [y]; field_simp [hs₀.ne']
    rw [hX, hY, mul_pow (2 * s) x, mul_pow (2 * s) y, hseq, hsub]
    field_simp [hs₀.ne']
  let S (m : ℕ) := ∑ i ∈ range m, hseq x y i
  let K (n : ℕ) := (2 * s) ^ (n + 3) / (Nat.factorial (n + 3) : ℝ)
  have hD (n : ℕ) : wDen s n = K n * (x * y * S (n + 1)) := by
    have he := hseq_gap hxy hsum (n + 1)
    change 1 - hseq x y (n + 1 + 1) = x * y * S (n + 1) at he
    rw [← he]
    unfold wDen K
    rw [show n + 3 = n + 2 + 1 by omega, hScale (n + 2)]
    field_simp [hs₀.ne']
  have hN (n : ℕ) : wNum s n = K n * ((n + 3 : ℕ) * hseq x y (n + 1) / (2 * s ^ 2)) := by
    have hn : (n + 3).factorial = (n + 3) * (n + 2).factorial :=
      Nat.factorial_succ (n + 2)
    have hp : (2 * s) ^ (n + 3) = (2 * s) ^ (n + 2) * (2 * s) := pow_succ _ _
    unfold wNum K
    rw [hScale (n + 1), hn, hp, Nat.cast_mul]
    push_cast
    field_simp [hs₀.ne']
  have hK (n : ℕ) : 0 < K n := by dsimp [K]; positivity
  have hS (n : ℕ) : 0 < S (n + 1) := by
    rw [show S (n + 1) = (∑ i ∈ range n, hseq x y (i + 1)) + hseq x y 0 by
      exact sum_range_succ' _ _]
    exact add_pos_of_nonneg_of_pos (sum_nonneg fun i _ => (hseq_pos hys hxy _).le)
      (hseq_pos hys hxy 0)
  have hDpos (n : ℕ) : 0 < wDen s n := by
    rw [hD n]
    exact mul_pos (hK n) (mul_pos (mul_pos (hys.trans hxy) hys) (hS n))
  refine ⟨hDpos, ?_⟩
  have he (n : ℕ) : wNum s n / wDen s n =
      1 / (2 * s ^ 2 * (x * y) * (S (n + 1) / ((n + 3 : ℕ) * hseq x y (n + 1)))) := by
    rw [hN, hD]
    field_simp [(hK n).ne', (hS n).ne', (hseq_pos hys hxy (n + 1)).ne',
      hs₀.ne', hys.ne', (hys.trans hxy).ne']
  intro i j hij
  change wNum s j / wDen s j ≤ wNum s i / wDen s i
  rw [he, he]
  have hk : 0 < 2 * s ^ 2 * (x * y) := by positivity
  apply one_div_le_one_div_of_le (mul_pos hk (div_pos (hS i)
    (mul_pos (by positivity) (hseq_pos hys hxy (i + 1)))))
  exact mul_le_mul_of_nonneg_left
    (hseq_mean_mono hys hxy hsum (Nat.add_le_add_right hij 1)) hk.le

private lemma w_antitone {s : ℝ} (hs : 1 < s) : AntitoneOn (fun q => w q s) (Set.Ioi 0) := by
  intro x hx y hy hxy
  change w y s ≤ w x s
  rw [w_ratio, w_ratio]
  obtain ⟨hpos, hcoef⟩ := w_coefficients hs
  have hp (q : ℝ) (hq : 0 < q) :
      0 < Real.exp (2 * s * q) - 1 - s * (Real.exp ((s + 1) * q) - Real.exp ((s - 1) * q)) := by
    rw [← (w_series_den s q).tsum_eq]
    exact (w_series_den s q).summable.tsum_pos (fun i => mul_nonneg (hpos i).le (pow_nonneg hq.le _))
      0 (mul_pos (hpos 0) (pow_pos hq _))
  apply (div_le_div_iff₀ (hp y hy) (hp x hx)).2
  simpa only [mul_comm] using
    (series_cross_le (e := fun i => i + 3) (fun _ _ h => by dsimp; omega)
      (fun i j hij => by
        simpa only [mul_comm] using (div_le_div_iff₀ (hpos j) (hpos i)).1 (hcoef hij))
      (le_of_lt hx) hxy (w_series_den s x) (w_series_den s y)
      (w_series_num s x) (w_series_num s y))

/-! ### The differential inequality -/

private lemma differential_ordered {a b s : ℝ} (hb : 0 < b) (hba : b ≤ a) (hs : 1 < s) :
    (halfDiff a b) ^ 2 / 3 * avg (w a s) (w b s) * radialU a b s ≤ differential a b s := by
  have ha := hb.trans_le hba
  let c := avg a b
  let d := halfDiff a b
  let D := halfDiff (p a s) (p b s)
  let D' := halfDiff (p₁ a s) (p₁ b s)
  let S := P₀ a b s - c
  obtain ⟨hD, hD'hi⟩ := p_halfDiff_bounds hb hba hs
  obtain ⟨hDd, hD'⟩ := p_halfDiff_transport hb hba hs
  have hc : 0 ≤ c := by dsimp [c, avg]; positivity
  have hS : 0 ≤ S := by
    dsimp [S, P₀, c, avg]
    linarith only [p_gt_q ha hs, p_gt_q hb hs]
  have hw : 0 ≤ avg (w a s) (w b s) := by
    unfold avg
    exact div_nonneg (add_nonneg (w_pos ha hs.le hs).le (w_pos hb hs.le hs).le) (by norm_num)
  have hZ : c * (d - D) - D' = (2 * D - d) * S - halfDiff (w a s) (w b s) := by
    dsimp [c, d, D, D', S, avg, halfDiff, P₀, p₁, w]
    ring
  have hsign := fourth_lower_bound c d D D' S (w a s) (w b s) (j a s) (j b s)
    hc hD hDd hD' hD'hi hS hw (w_antitone hs hb ha hba) (j_antitone hs hb ha hba) hZ
  have hA (q : ℝ) : q * p q s + w q s = A₂ q s := by unfold w; ring
  have hB (q : ℝ) : q * A₂ q s + j q s = A₃ q s := by unfold j; ring
  have hh := fourth_factor_algebra a b (p a s) (p b s) (w a s) (w b s) (j a s) (j b s)
  dsimp only at hh
  rw [hA a, hA b, hB a, hB b] at hh
  have hjets := radialU_jets ha hb s hs
  unfold differential
  rw [hjets.1, hjets.2, ← mul_assoc, ← sub_mul]
  change _ ≤ (P₃ a b s + 4 * P₀ a b s * P₂ a b s + 3 * P₁ a b s ^ 2 +
    6 * P₀ a b s ^ 2 * P₁ a b s + P₀ a b s ^ 4 - c ^ 2 * (P₁ a b s + P₀ a b s ^ 2)) * _
  exact mul_le_mul_of_nonneg_right (hsign.trans_eq hh.symm) (radialU_pos ha hb hs).le

/-- Proposition 4.4, including the quantitative lower bound. -/
private theorem differential_quantitative {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 1 < s) :
    (halfDiff a b) ^ 2 / 3 * avg (w a s) (w b s) * radialU a b s ≤ differential a b s := by
  rcases le_total b a with h | h
  · exact differential_ordered hb h hs
  · have hU : radialU b a = radialU a b := by funext t; simp [radialU, mul_comm]
    have hD : differential b a s = differential a b s := by simp [differential, hU, midpoint, add_comm]
    have hhalf : halfDiff b a ^ 2 = halfDiff a b ^ 2 := by unfold halfDiff; ring
    have hw : avg (w b s) (w a s) = avg (w a s) (w b s) := by unfold avg; ring
    simpa only [hD, hU, hhalf, hw] using differential_ordered ha h hs

/-- The sign of `U⁽⁴⁾ - c² U''` on the open half-line. -/
private theorem differential_pos_domain (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) (hs : 1 < s) :
    0 ≤ differential a b s := by
  apply le_trans _ (differential_quantitative ha hb hs)
  exact mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
    (div_nonneg (add_nonneg (w_pos ha hs.le hs).le (w_pos hb hs.le hs).le) (by norm_num)))
    (radialU_pos ha hb hs).le

end DifferentialInequality

private lemma differential_nonneg (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) (hs : 1 ≤ s) :
    0 ≤ differential a b s := by
  rcases eq_or_lt_of_le hs with h | h
  · subst s
    have hSmooth := radialU_smooth a b 1 ha hb le_rfl
    have hc : ContinuousAt (differential a b) 1 :=
      (smooth_iterated hSmooth 4).continuousAt.sub
        ((smooth_iterated hSmooth 2).continuousAt.const_mul (midpoint a b ^ 2))
    have ht : Tendsto (differential a b) (𝓝[>] (1 : ℝ)) (𝓝 (differential a b 1)) :=
      hc.continuousWithinAt
    have hgt : ∀ᶠ u : ℝ in 𝓝[>] (1 : ℝ), u ∈ Set.Ioi (1 : ℝ) :=
      self_mem_nhdsWithin
    exact ge_of_tendsto ht (hgt.mono fun u hu => differential_pos_domain a b u ha hb hu)
  · exact differential_pos_domain a b s ha hb h

/-- The geometric-mean harmonic minorant, on the circle in logarithmic radii.
Both positive denominators have been cleared. -/
def KernelBound (n : ℕ) : Prop :=
  ∀ (a b : ℝ), 0 < a → 0 < b → ∀ z : ℂ, ‖z‖ = 1 →
    0 ≤ meanTerm n a b * radii a b n -
      (Real.cosh (midpoint a b) - z.re) * fourierNumerator (radii a b) z n

/-! ## Harmonic extension and the Gram sum -/

private def poisson (z : ℂ) : ℝ := ((1 + z) / (1 - z)).re

private lemma poisson_normSq (z : ℂ) : poisson z = (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
  unfold poisson
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.normSq_apply]
  ring

private lemma poisson_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) : 0 ≤ poisson z := by
  rw [poisson_normSq, ← Complex.sq_norm]
  exact div_nonneg (sub_nonneg.mpr (by simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hz))
    (Complex.normSq_nonneg _)

private lemma exp_neg_mul_hyp (c : ℝ) :
    2 * Real.exp (-c) * Real.cosh c = 1 + Real.exp (-c) ^ 2 ∧
    2 * Real.exp (-c) * Real.sinh c = 1 - Real.exp (-c) ^ 2 := by
  have h : Real.exp (-c) * Real.exp c = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  constructor
  · rw [Real.cosh_eq]; linarith only [h]
  · rw [Real.sinh_eq]; linarith only [h]

private lemma poisson_circle (c : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    poisson ((Real.exp (-c) : ℂ) * z) = Real.sinh c / (Real.cosh c - z.re) := by
  let r := Real.exp (-c)
  have hr := (Real.exp_pos (-c)).ne'
  have hz' : Complex.normSq z = 1 := by rw [← Complex.sq_norm, hz, one_pow]
  have ht : Complex.normSq ((r : ℂ) * z) = r ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, hz', mul_one, sq]
  have hd : Complex.normSq (1 - (r : ℂ) * z) = 2 * r * (Real.cosh c - z.re) := by
    rw [Complex.normSq_sub, Complex.normSq_one, ht]
    simp only [one_mul, Complex.conj_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have h := (exp_neg_mul_hyp c).1
    change 2 * r * Real.cosh c = 1 + r ^ 2 at h
    linarith only [h]
  rw [poisson_normSq, ht, hd]
  change (1 - r ^ 2) / _ = _
  have h := (exp_neg_mul_hyp c).2
  change 2 * r * Real.sinh c = 1 - r ^ 2 at h
  rw [← h, mul_div_mul_left _ _ (mul_ne_zero (by norm_num) hr)]

/-- Poisson averaging transports a boundary inequality for the real part
of a holomorphic function to the entire closed disk. -/
private lemma re_nonneg_disk {F : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ F (Metric.closedBall 0 1))
    (hb : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (F z).re)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : 0 ≤ (F z).re := by
  rcases lt_or_eq_of_le hz with hz' | hz'
  · have hh : InnerProductSpace.HarmonicOnNhd (fun w => (F w).re) (Metric.closedBall 0 1) :=
      fun w hw => (hf w hw).harmonicAt_re
    have hw : z ∈ Metric.ball (0 : ℂ) 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz'
    rw [← hh.circleAverage_poissonKernel_smul hw]
    apply Real.circleAverage_nonneg_of_nonneg
    intro w hw'
    have hw'' : ‖w‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hw'
    change 0 ≤ poissonKernel 0 z w * (F w).re
    apply mul_nonneg _ (hb w hw'')
    rw [poissonKernel_def, sub_zero, sub_zero, hw'']
    exact div_nonneg (sub_nonneg.mpr (by simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hz))
      (sq_nonneg _)
  · exact hb z hz'

private lemma H_nat_nonneg {a : ℝ} (ha : 0 < a) (m : ℕ) : 0 ≤ H a m := by
  by_cases hm : m ≤ 1
  · have h : m = 0 ∨ m = 1 := by omega
    rcases h with rfl | rfl <;> simp [H]
  · apply (H_pos ha _).le
    exact_mod_cast (show 1 < m by omega)

private def coefficient (n : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (H a ((n - k : ℕ) : ℝ) / H a n)

private def harmonicMinorant (n : ℕ) (a b : ℝ) (z : ℂ) : ℝ :=
  ∑ k ∈ range n, coefficient n a k * coefficient n b k * cosine z k

private lemma radii_sqrt (a b : ℝ) (m : ℕ) :
    radii a b m = Real.sqrt (H a m * H b m) := by
  cases m with
  | zero => simp [radii, radialU, H]
  | succ m =>
    have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast (show 1 ≤ m + 1 by omega)
    exact ite_eq_right (not_lt.mpr hm)

private lemma numerator_minorant (n : ℕ) (hn : 3 ≤ n) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    fourierNumerator (radii a b) z n = radii a b n * harmonicMinorant n a b z := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hab := mul_pos (H_pos ha hn') (H_pos hb hn')
  have hr : radii a b n ≠ 0 := by rw [radii_sqrt]; exact (Real.sqrt_pos.2 hab).ne'
  have hk (k : ℕ) : coefficient n a k * coefficient n b k = radii a b (n - k) / radii a b n := by
    unfold coefficient
    rw [radii_sqrt, radii_sqrt, ← Real.sqrt_mul (div_nonneg (H_nat_nonneg ha _) (H_pos ha hn').le),
      div_mul_div_comm, Real.sqrt_div (mul_nonneg (H_nat_nonneg ha _) (H_nat_nonneg hb _))]
  unfold fourierNumerator harmonicMinorant
  rw [← Finset.sum_range_reflect, mul_sum]
  apply sum_congr rfl
  intro k hkm
  have hk' := mem_range.mp hkm
  rw [hk, ← mul_assoc, mul_div_cancel₀ _ hr]
  rw [show n - 1 - (n - 1 - k) = k by omega, show n - 1 - k + 1 = n - k by omega]

private lemma logWeight_pos (n : ℕ) (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a) :
    0 < logWeight n a := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  exact div_pos (sub_pos.mpr (Real.one_lt_cosh.mpr (mul_pos (by linarith) ha).ne')) (H_pos ha hn')

private lemma minorant_disk {n : ℕ} (hn : 3 ≤ n) (kernel : KernelBound n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    harmonicMinorant n a b z ≤
      Real.sqrt (logWeight n a * logWeight n b) *
        poisson ((Real.exp (-(midpoint a b)) : ℂ) * z) := by
  let c := midpoint a b
  let r := Real.exp (-c)
  let M := Real.sqrt (logWeight n a * logWeight n b)
  have hc : 0 < c := by unfold c midpoint; linarith
  have hr : r < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)
  let poly (z : ℂ) : ℂ := ∑ k ∈ range n,
    ((coefficient n a k * coefficient n b k * (if k = 0 then 1 else 2) : ℝ) : ℂ) * z ^ k
  have poly_re (z : ℂ) : (poly z).re = harmonicMinorant n a b z := by
    unfold poly harmonicMinorant
    rw [Complex.re_sum]
    apply sum_congr rfl
    intro k _
    cases k <;> simp [cosine, Complex.mul_re, mul_assoc]
  let F (z : ℂ) : ℂ := (M : ℂ) * ((1 + (r : ℂ) * z) / (1 - (r : ℂ) * z)) - poly z
  have hF (z : ℂ) : (F z).re = M * poisson ((r : ℂ) * z) - harmonicMinorant n a b z := by
    simp only [F, Complex.sub_re, poly_re, poisson, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hf : AnalyticOnNhd ℂ F (Metric.closedBall 0 1) := by
    intro w hw
    have hw' : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
    have hwn : (1 : ℂ) - (r : ℂ) * w ≠ 0 := by
      apply sub_ne_zero.mpr
      intro he
      have he' := congrArg norm he
      simp only [norm_one, norm_mul, Complex.norm_of_nonneg (show 0 ≤ r from (Real.exp_pos _).le)] at he'
      nlinarith [norm_nonneg w, mul_le_mul_of_nonneg_left hw' (Real.exp_pos (-c)).le]
    unfold F
    exact (analyticAt_const.mul
      ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).div
        (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) hwn)).sub
      (Finset.analyticAt_fun_sum _ (fun k _ => analyticAt_const.mul (analyticAt_id.pow k)))
  have hboundary (w : ℂ) (hw : ‖w‖ = 1) : 0 ≤ (F w).re := by
    have h := kernel a b ha hb w hw
    rw [numerator_minorant n hn ha hb] at h
    have hcos : 0 < Real.cosh c - w.re := by
      have h := (le_abs_self w.re).trans (Complex.abs_re_le_norm w)
      rw [hw] at h
      exact sub_pos.mpr (h.trans_lt (Real.one_lt_cosh.mpr hc.ne'))
    have hu : 0 < radii a b n := by
      rw [radii_sqrt]
      have h : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      exact Real.sqrt_pos.2 (mul_pos (H_pos ha h) (H_pos hb h))
    rw [hF, poisson_circle c w hw, sub_nonneg, ← mul_div_assoc]
    apply (le_div_iff₀ hcos).2
    unfold meanTerm at h
    change 0 ≤ M * Real.sinh c * radii a b n -
      (Real.cosh c - w.re) * (radii a b n * harmonicMinorant n a b w) at h
    have h' : harmonicMinorant n a b w * (Real.cosh c - w.re) ≤ M * Real.sinh c := by
      apply le_of_mul_le_mul_right ?_ hu
      linarith only [h]
    exact h'
  have hs := re_nonneg_disk hf hboundary hz
  rwa [hF, sub_nonneg] at hs

private lemma H_adjacent (q s : ℝ) :
    H q (s + 1) + H q (s - 1) - 2 * Real.cosh q * H q s =
      2 * s * (Real.cosh q - 1) * Real.sinh q := by
  unfold H
  rw [add_mul, sub_mul, one_mul, Real.sinh_add, Real.sinh_sub]
  ring

private lemma equal_radii {a : ℝ} (ha : 0 < a) (m : ℕ) : radii a a m = H a m := by
  rw [radii_sqrt, ← sq, Real.sqrt_sq (H_nat_nonneg ha _)]

private lemma equal_auxiliary {a : ℝ} (ha : 0 < a) (m : ℕ) :
    auxiliary (radii a a) (Real.cosh a) m = (m : ℝ) * ((Real.cosh a - 1) * Real.sinh a) := by
  cases m with
  | zero => simp [auxiliary]
  | succ m =>
    simp only [auxiliary, equal_radii ha, Nat.cast_succ]
    have h := H_adjacent a ((m : ℝ) + 1)
    rw [show (m : ℝ) + 1 - 1 = m by ring] at h
    linarith only [h]

/-- The exact equal-radius correction obtained by evaluating the Fejér
identity at 1. This is the same correction as averaging over μ_n. -/
private lemma diagonal_poisson {n : ℕ} (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a) :
    logWeight n a * poisson (Real.exp (-a) : ℂ) - harmonicMinorant n a a 1 =
      n * (logWeight n a * poisson (Real.exp (-(n * a)) : ℂ) - 1) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hx := H_pos ha hn'
  have hc := sub_pos.mpr (Real.one_lt_cosh.mpr ha.ne')
  have hnc := sub_pos.mpr (Real.one_lt_cosh.mpr (mul_pos (by linarith : (0 : ℝ) < n) ha).ne')
  let C := Real.cosh a
  let E := (C - 1) * Real.sinh a
  let U := radii a a
  have hB (j : ℕ) : fejerWeight U C j = if j = 0 then E else 0 := by
    rcases j with _ | _ | j
    · simp [fejerWeight, U, C, E, equal_auxiliary ha]
    · simp [fejerWeight, U, C, E, equal_auxiliary ha]
    · simp [fejerWeight, U, C, E, equal_auxiliary ha, Nat.cast_add]; ring
  have hh : (∑ j ∈ range n, fejerWeight U C j * ‖geom (n - j) (1 : ℂ)‖ ^ 2) = E * (n : ℝ) ^ 2 := by
    rw [sum_eq_single 0]
    · simp [hB, geom]
    · intro j hj hj0
      simp [hB, hj0]
    · intro hn0
      exact (hn0 (mem_range.mpr (by omega))).elim
  have hs := fourier_sos U C (logWeight n a * Real.sinh a) hn
    (by simp [U, equal_radii ha, H]) (by simp [U, equal_radii ha, H]) 1 norm_one
  rw [hh, numerator_minorant n hn ha ha] at hs
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := Nat.cast_sub (by omega)
  simp only [U, C, Complex.one_re, equal_radii ha, Nat.cast_add_one, hcast, H_difference] at hs
  have hposDiv (q : ℝ) : poisson (Real.exp (-q) : ℂ) =
      Real.sinh q / (Real.cosh q - 1) := by
    simpa only [mul_one, Complex.one_re] using poisson_circle q 1 norm_one
  have hw : logWeight n a * H a n = Real.cosh (n * a) - 1 :=
    div_mul_cancel₀ _ hx.ne'
  have hmain : logWeight n a * poisson (Real.exp (-a) : ℂ) - harmonicMinorant n a a 1 =
      (n : ℝ) ^ 2 * Real.sinh a / H a n := by
    rw [hposDiv]
    apply (eq_div_iff hx.ne').2
    field_simp [hc.ne']
    dsimp [E, C] at hs
    have hprod := congrArg (· * Real.sinh a) hw
    linear_combination hs + hprod
  rw [hmain, hposDiv]
  unfold logWeight
  field_simp [hx.ne', hnc.ne']
  unfold H
  ring

private lemma gram_power_pos {n : ℕ} {C : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (k : ℕ) :
    (Matrix.of fun i j => C i j ^ (k + 1)).PosSemidef := by
  induction k with
  | zero =>
    have hEq : Matrix.of (fun i j => C i j ^ (0 + 1 : ℕ)) = C := by
      ext i j
      simp
    rw [hEq]
    exact hC
  | succ k ih =>
    have he : (Matrix.of fun i j => C i j ^ (k + 1)) ⊙ C =
        Matrix.of (fun i j => C i j ^ (k + 1 + 1)) := by
      ext i j
      simp [pow_succ]
    rw [← he]
    exact ih.hadamard hC

private lemma weighted_gram_nonneg {n : ℕ} {C : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (p : Fin n → ℝ) {k : ℕ} (hk : 0 < k) :
    0 ≤ ∑ i, ∑ j, p i * p j * (C i j ^ k).re := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  let V : Fin n → ℂ := fun i => p i
  have h := (gram_power_pos hC m).re_dotProduct_nonneg V
  change 0 ≤ Complex.re (dotProduct (star V)
    (Matrix.mulVec (Matrix.of fun i j => C i j ^ (m + 1)) V)) at h
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Complex.re_sum, Pi.star_apply, V, Complex.star_def,
    Complex.conj_ofReal, Finset.mul_sum, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at h
  convert h using 1
  congr 1
  funext i
  apply sum_congr rfl
  intro j _
  ring

private lemma harmonic_sum_lower {n : ℕ} (hn : 3 ≤ n)
    {C : Matrix (Fin n) (Fin n) ℂ} (hC : C.PosSemidef)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    (n : ℝ) ^ 2 ≤ ∑ i, ∑ j, harmonicMinorant n (a i) (a j) (C i j) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have h0 (i : Fin n) : coefficient n (a i) 0 = 1 := by
    simp [coefficient, (H_pos (ha i) hn').ne']
  let S (k : ℕ) := ∑ i : Fin n, ∑ j : Fin n, coefficient n (a i) k * coefficient n (a j) k *
    cosine (C i j) k
  have hs : (∑ i, ∑ j, harmonicMinorant n (a i) (a j) (C i j)) = ∑ k ∈ range n, S k := by
    unfold harmonicMinorant
    let term (i j : Fin n) (k : ℕ) :=
      coefficient n (a i) k * coefficient n (a j) k * cosine (C i j) k
    calc
      _ = ∑ i, ∑ k ∈ range n, ∑ j, term i j k :=
        sum_congr rfl (fun _ _ => sum_comm)
      _ = _ := sum_comm
  have hn0 : 0 ∈ range n := mem_range.mpr (by omega)
  have hz : S 0 = (n : ℝ) ^ 2 := by simp [S, h0, cosine, pow_two]
  rw [hs, ← sum_erase_add _ _ hn0, hz]
  apply le_add_of_nonneg_left
  apply sum_nonneg
  intro k hk
  have hk' : k ≠ 0 := (mem_erase.mp hk).1
  cases k with
  | zero => exact (hk' rfl).elim
  | succ k =>
    have h := weighted_gram_nonneg hC (fun i => coefficient n (a i) (k + 1))
      (k := k + 1) (Nat.succ_pos _)
    have he : S (k + 1) =
        2 * ∑ i, ∑ j, coefficient n (a i) (k + 1) * coefficient n (a j) (k + 1) *
          (C i j ^ (k + 1)).re := by
      simp only [S, cosine, mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    rw [he]
    exact mul_nonneg (by norm_num) h

private lemma gram_poisson_bound {n : ℕ} (hn : 3 ≤ n) (kernel : KernelBound n)
    {C : Matrix (Fin n) (Fin n) ℂ} (hC : C.PosSemidef)
    (hdiag : ∀ i, C i i = 1) {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    n * (∑ i, logWeight n (a i) * poisson (Real.exp (-(n * a i)) : ℂ)) ≤
      ∑ i, ∑ j, ((logWeight n (a i) + logWeight n (a j)) / 2) *
        poisson ((Real.exp (-(midpoint (a i) (a j))) : ℂ) * C i j) := by
  let D (i : Fin n) := n * (logWeight n (a i) * poisson (Real.exp (-(n * a i)) : ℂ) - 1)
  have hpair (i j : Fin n) : harmonicMinorant n (a i) (a j) (C i j) + (if j = i then D i else 0) ≤
      ((logWeight n (a i) + logWeight n (a j)) / 2) *
        poisson ((Real.exp (-(midpoint (a i) (a j))) : ℂ) * C i j) := by
    by_cases h : j = i
    · subst j
      simp only [hdiag, ite_true, mul_one, D, show midpoint (a i) (a i) = a i by
        unfold midpoint; ring, show (logWeight n (a i) + logWeight n (a i)) / 2 =
          logWeight n (a i) by ring]
      linarith only [diagonal_poisson hn (ha i)]
    · rw [ite_eq_right h, add_zero]
      have hnorm : ‖C i j‖ ≤ 1 := by
        apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).1
        simpa [hdiag] using entry_sq_le hC i j
      have hmid : 0 < midpoint (a i) (a j) := by unfold midpoint; linarith [ha i, ha j]
      have hr := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hmid)
      have hnrm : ‖(Real.exp (-(midpoint (a i) (a j))) : ℂ) * C i j‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
        exact (mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le).trans (by simpa using hr.le)
      have hw₁ := logWeight_pos n hn (ha i)
      have hw₂ := logWeight_pos n hn (ha j)
      have hmean : Real.sqrt (logWeight n (a i) * logWeight n (a j)) ≤
          (logWeight n (a i) + logWeight n (a j)) / 2 := by
        apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
        rw [Real.sq_sqrt (mul_nonneg hw₁.le hw₂.le)]
        nlinarith [sq_nonneg (logWeight n (a i) - logWeight n (a j))]
      exact (minorant_disk hn kernel (ha i) (ha j) hnorm).trans
        (mul_le_mul_of_nonneg_right hmean (poisson_nonneg hnrm))
  have h := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) =>
    sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin n))) => hpair i j)
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true] at h
  have hD : (∑ i, D i) = n * (∑ i, logWeight n (a i) * poisson (Real.exp (-(n * a i)) : ℂ)) -
      (n : ℝ) ^ 2 := by simp [D, mul_sub, sum_sub_distrib, ← mul_sum, pow_two]
  rw [hD] at h
  linarith only [h, harmonic_sum_lower hn hC ha]

/-! ## The backward radial flow -/

private lemma reciprocal_weight_tendsto (n : ℕ) (hn : 3 ≤ n) :
    Tendsto (fun q => (logWeight n q)⁻¹) atTop (𝓝 1) := by
  let N := (n : ℝ)
  have hN : 3 ≤ N := by dsimp [N]; exact_mod_cast hn
  let e (k q : ℝ) := Real.exp (-(k * q))
  have he (k : ℝ) (hk : 0 < k) : Tendsto (e k) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_id.const_mul_atTop hk))
  have h₁ := he N (by linarith)
  have h₂ := he (2 * N) (by linarith)
  have h₃ := he (N - 1) (by linarith)
  have h₄ := he (N + 1) (by linarith)
  have hlim : Tendsto (fun q => (1 - e (2 * N) q - N * (e (N - 1) q - e (N + 1) q)) /
      (1 + e (2 * N) q - 2 * e N q)) atTop (𝓝 1) := by
    convert ((tendsto_const_nhds.sub h₂).sub ((h₃.sub h₄).const_mul N)).div
      ((tendsto_const_nhds.add h₂).sub (h₁.const_mul (2 : ℝ))) (by norm_num : (1 : ℝ) + 0 - 2 * 0 ≠ 0)
      using 1
    norm_num
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with q hq
  have hq' : 0 < q := by linarith
  have hpos := Real.one_lt_cosh.mpr (mul_pos (by linarith : 0 < N) hq').ne'
  have he₀ := Real.exp_pos (-(N * q))
  have pp : 2 * e N q * (Real.cosh (N * q) - 1) =
      1 + e (2 * N) q - 2 * e N q := by
    have h := (exp_neg_mul_hyp (N * q)).1
    have hpow : e N q ^ 2 = e (2 * N) q := by
      dsimp [e]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    change 2 * e N q * Real.cosh (N * q) = 1 + e N q ^ 2 at h
    linarith only [h, hpow]
  have pq : 2 * e N q * H q N = 1 - e (2 * N) q - N * (e (N - 1) q - e (N + 1) q) := by
    have h := (exp_neg_mul_hyp (N * q)).2
    have hpow : e N q ^ 2 = e (2 * N) q := by
      dsimp [e]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hmul : 2 * e N q * Real.sinh q = e (N - 1) q - e (N + 1) q := by
      dsimp only [e]
      rw [Real.sinh_eq]
      have h₁' : Real.exp (-(N * q)) * Real.exp q = Real.exp (-((N - 1) * q)) := by
        rw [← Real.exp_add]; congr 1; ring
      have h₂' : Real.exp (-(N * q)) * Real.exp (-q) = Real.exp (-((N + 1) * q)) := by
        rw [← Real.exp_add]; congr 1; ring
      linarith only [h₁', h₂']
    change 2 * e N q * Real.sinh (N * q) = 1 - e N q ^ 2 at h
    unfold H
    have hh := congrArg (N * ·) hmul
    linarith only [h, hpow, hh]
  rw [← pp, ← pq, mul_div_mul_left _ _ (mul_ne_zero (by norm_num) he₀.ne')]
  simp [logWeight, N, inv_div]

/-- The integrated reciprocal speed defines the backward flow by scalar
inversion. In logarithmic radii the desired flow moves towards +∞. The
constant extension below a₀ gives an order isomorphism of the real line. -/
private lemma exists_backward_flow (n : ℕ) (hn : 3 ≤ n) (a₀ : ℝ) (ha₀ : 0 < a₀) :
    ∃ a : ℝ → ℝ, a 0 = a₀ ∧
      (∀ t, 0 ≤ t → a₀ ≤ a t ∧ HasDerivAt a (logWeight n (a t)) t) ∧
      Tendsto a atTop atTop := by
  let g (q : ℝ) := (logWeight n (max a₀ q))⁻¹
  have hg (q : ℝ) : 0 < g q := inv_pos.mpr
    (logWeight_pos n hn (ha₀.trans_le (le_max_left _ _)))
  have hgc : Continuous g := by
    have hc : Continuous (fun q : ℝ => max a₀ q) := continuous_const.max continuous_id
    have hd : Continuous (fun q : ℝ => H (max a₀ q) n) := by unfold H; fun_prop
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hd' (q : ℝ) : H (max a₀ q) n ≠ 0 :=
      (H_pos (ha₀.trans_le (le_max_left a₀ q)) hn').ne'
    have hw : Continuous (fun q : ℝ => logWeight n (max a₀ q)) := by
      apply Continuous.div _ hd hd'
      fun_prop
    exact hw.inv₀ (fun q => (logWeight_pos n hn (ha₀.trans_le (le_max_left _ _))).ne')
  let T (q : ℝ) := ∫ u in a₀..q, g u
  have hT (q : ℝ) : HasDerivAt T (g q) q :=
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      hgc.stronglyMeasurable.stronglyMeasurableAtFilter hgc.continuousAt
  have hTc : Continuous T :=
    continuous_iff_continuousAt.mpr (fun q => (hT q).continuousAt)
  have hmono : StrictMono T := strictMono_of_deriv_pos (fun q => by rw [(hT q).deriv]; exact hg q)
  have htend : Tendsto g atTop (𝓝 1) := by
    apply (reciprocal_weight_tendsto n hn).congr'
    filter_upwards [eventually_ge_atTop a₀] with q hq
    simp [g, max_eq_right hq]
  obtain ⟨w, hw⟩ := eventually_atTop.1
    (htend.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  have htop : Tendsto T atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop (max w (w + 2 * (B - T w)))] with q hq
    have hq₁ := (le_max_left _ _).trans hq
    have hq₂ := (le_max_right _ _).trans hq
    have he : T w + (∫ x in w..q, g x) = T q :=
      intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
    have hle : (∫ x in w..q, (1 / 2 : ℝ)) ≤ ∫ x in w..q, g x :=
      intervalIntegral.integral_mono_on hq₁ intervalIntegrable_const (hgc.intervalIntegrable _ _)
        (fun x hx => (hw x hx.1).le)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hle
    linarith
  have hbot : Tendsto T atBot atBot := by
    apply ((tendsto_atBot_add_const_right _ (-a₀) tendsto_id).const_mul_atBot (hg a₀)).congr'
    filter_upwards [eventually_le_atBot a₀] with q hq
    change g a₀ * (q + -a₀) = ∫ u in a₀..q, g u
    rw [show (∫ u in a₀..q, g u) = ∫ _ in a₀..q, g a₀ by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_ge hq] at hu
      dsimp only [g]
      rw [max_eq_left hu.2, max_self]]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  let E := hmono.orderIsoOfSurjective T (hTc.surjective htop hbot)
  have h0 : T a₀ = 0 := intervalIntegral.integral_same
  have hE : E a₀ = 0 := h0
  have hE0 : E.symm 0 = a₀ := by rw [← hE, E.symm_apply_apply]
  refine ⟨E.symm, hE0, ?_, E.symm.tendsto_atTop⟩
  intro t ht
  have hbound : a₀ ≤ E.symm t := hE0 ▸ E.symm.monotone ht
  refine ⟨hbound, ?_⟩
  have hleft : ∀ᶠ y in 𝓝 t, T (E.symm y) = y :=
    Eventually.of_forall E.apply_symm_apply
  have hd := (hT (E.symm t)).of_local_left_inverse E.symm.continuous.continuousAt
    (hg _).ne' hleft
  simpa [g, max_eq_right hbound] using hd

private lemma exp_entry_norm_lt {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(Real.exp (-a) : ℂ) * z‖ < 1 := by
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (-a) * 1 := mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le
    _ < _ := by simpa using Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)

private lemma normSq_exp_entry (r : ℝ) (z : ℂ) :
    Complex.normSq (1 - (r : ℂ) * z) = 1 + r ^ 2 * Complex.normSq z - 2 * r * z.re := by
  rw [Complex.normSq_sub, Complex.normSq_one, Complex.normSq_mul, Complex.normSq_ofReal]
  simp only [one_mul, Complex.conj_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

private lemma log_entry_deriv {a : ℝ → ℝ} {t a' : ℝ} (hd : HasDerivAt a a' t)
    (ha : 0 < a t) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasDerivAt (fun u => Real.log ‖(1 : ℂ) - (Real.exp (-(a u)) : ℂ) * z‖)
      (a' * (poisson ((Real.exp (-(a t)) : ℂ) * z) - 1) / 2) t := by
  let r (u : ℝ) := Real.exp (-(a u))
  let S := Complex.normSq z
  let N (u : ℝ) := 1 + r u ^ 2 * S - 2 * r u * z.re
  have hr : HasDerivAt r (r t * -a') t := hd.neg.exp
  have hdN : HasDerivAt N (2 * a' * (r t * z.re - r t ^ 2 * S)) t := by
    have h := (((hr.pow 2).mul_const S).const_add 1).sub ((hr.const_mul 2).mul_const z.re)
    convert h using 1
    ring
  have hN (u : ℝ) : N u = Complex.normSq (1 - (r u : ℂ) * z) := (normSq_exp_entry _ _).symm
  have hn : N t ≠ 0 := by
    rw [hN, ne_eq, Complex.normSq_eq_zero]
    exact sub_ne_zero.mpr (fun he => (exp_entry_norm_lt ha hz).ne (by
      change ‖(r t : ℂ) * z‖ = 1
      rw [← he, norm_one]))
  have hPoisson : poisson ((r t : ℂ) * z) - 1 =
        2 * (r t * z.re - r t ^ 2 * S) / N t := by
    rw [poisson_normSq, ← hN, Complex.normSq_mul, Complex.normSq_ofReal]
    change (1 - r t * r t * S) / N t - 1 = _
    field_simp [hn]
    dsimp only [N]
    ring
  have hlog (u : ℝ) : Real.log ‖(1 : ℂ) - (r u : ℂ) * z‖ = Real.log (N u) / 2 := by
    rw [hN, Complex.normSq_eq_norm_sq, Real.log_pow]
    norm_num
  change HasDerivAt (fun u => Real.log ‖(1 : ℂ) - (r u : ℂ) * z‖)
    (a' * (poisson ((r t : ℂ) * z) - 1) / 2) t
  simp_rw [hlog, hPoisson]
  convert (hdN.log hn).div_const 2 using 1
  ring

private lemma from_full_strict_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hdiag : ∀ i, (A i i).re < 1)
    (h : (∏ i : Fin n, ∏ j : Fin n, ‖1 - A i j‖) ≤ ∏ i : Fin n, ‖1 - A i i ^ n‖) :
    Cancelled A := by
  have hrows (i : Fin n) :
      (∏ j : Fin n, ‖1 - A i j‖) =
        ‖1 - A i i‖ * ∏ j ∈ univ.erase i, ‖1 - A i j‖ :=
    (mul_prod_erase _ _ (mem_univ i)).symm
  have hpos : 0 < ∏ i : Fin n, ‖1 - A i i‖ := by
    apply prod_pos
    intro i _
    apply norm_pos_iff.mpr
    rw [ne_eq, sub_eq_zero]
    intro he
    have hi := congrArg Complex.re he
    have hit := hdiag i
    simp only [Complex.one_re] at hi
    linarith
  simp only [hrows, diag_factor hA, prod_mul_distrib] at h
  exact (mul_le_mul_iff_of_pos_left hpos).1 h

private lemma radial_flow_positive {n : ℕ} (hn : 3 ≤ n) (kernel : KernelBound n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (hpos : ∀ i, 0 < (A i i).re) (hdiag : ∀ i, (A i i).re < 1) : Cancelled A := by
  let a₀ (i : Fin n) := -Real.log (A i i).re
  have ha₀ (i : Fin n) : 0 < a₀ i := neg_pos.mpr (Real.log_neg (hpos i) (hdiag i))
  have he₀ (i : Fin n) : Real.exp (-(a₀ i)) = (A i i).re := by
    simp only [a₀, neg_neg, Real.exp_log (hpos i)]
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => (Real.exp (a₀ i / 2) : ℂ))
  let C := D * A * Dᴴ
  have hC : C.PosSemidef := hA.mul_mul_conjTranspose_same D
  have hCeq (i j : Fin n) : C i j =
      (Real.exp (midpoint (a₀ i) (a₀ j)) : ℂ) * A i j := by
    simp only [C, D, Matrix.diagonal_conjTranspose, Pi.star_apply, Complex.star_def,
      Complex.conj_ofReal, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [show midpoint (a₀ i) (a₀ j) = a₀ i / 2 + a₀ j / 2 by unfold midpoint; ring,
      Real.exp_add, Complex.ofReal_mul]
    ring
  have hback (i j : Fin n) : (Real.exp (-(midpoint (a₀ i) (a₀ j))) : ℂ) * C i j = A i j := by
    rw [hCeq, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, Complex.ofReal_one, one_mul]
  have hCdiag (i : Fin n) : C i i = 1 := by
    have hm : midpoint (a₀ i) (a₀ i) = a₀ i := by unfold midpoint; ring
    have h := hback i i
    rw [hm, he₀, diag_real hA i] at h
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (hpos i).ne') (h.trans (mul_one _).symm)
  have hCnorm (i j : Fin n) : ‖C i j‖ ≤ 1 := by
    apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
    simpa [hCdiag] using entry_sq_le hC i j
  choose a a_zero a_prop a_lim using fun i : Fin n => exists_backward_flow n hn (a₀ i) (ha₀ i)
  have hapos (i : Fin n) (t : ℝ) (ht : 0 ≤ t) : 0 < a i t :=
    (ha₀ i).trans_le (a_prop i t ht).1
  let z (i j : Fin n) (t : ℝ) := (Real.exp (-(midpoint (a i t) (a j t))) : ℂ) * C i j
  let y (i : Fin n) (t : ℝ) : ℂ := Real.exp (-(n * a i t))
  let Q (t : ℝ) := (∑ i, Real.log ‖1 - y i t‖) - ∑ i, ∑ j, Real.log ‖1 - z i j t‖
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hder (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt Q
        ((∑ i, (n * logWeight n (a i t)) * (poisson (y i t) - 1) / 2) -
          ∑ i, ∑ j, ((logWeight n (a i t) + logWeight n (a j t)) / 2) *
            (poisson (z i j t) - 1) / 2) t := by
    unfold Q
    apply HasDerivAt.sub
    · apply HasDerivAt.fun_sum (u := univ) (A := fun i u => Real.log ‖1 - y i u‖)
      intro i _
      simpa only [y, mul_one] using log_entry_deriv ((a_prop i t ht).2.const_mul (n : ℝ))
        (mul_pos hnr (hapos i t ht)) (z := (1 : ℂ)) (le_of_eq norm_one)
    · apply HasDerivAt.fun_sum (u := univ) (A := fun i u => ∑ j, Real.log ‖1 - z i j u‖)
      intro i _
      apply HasDerivAt.fun_sum (u := univ) (A := fun j u => Real.log ‖1 - z i j u‖)
      intro j _
      have hmid : 0 < midpoint (a i t) (a j t) := by unfold midpoint; linarith [hapos i t ht, hapos j t ht]
      exact log_entry_deriv (((a_prop i t ht).2.add (a_prop j t ht).2).div_const 2) hmid (hCnorm i j)
  have hmono : AntitoneOn Q (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : 0 < t := by simpa using ht
      exact (hder t ht'.le).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 ≤ t := (show 0 < t by simpa using ht).le
      rw [(hder t ht').deriv]
      have h := gram_poisson_bound hn kernel hC hCdiag (fun i => hapos i t ht')
      change (n : ℝ) * (∑ i, logWeight n (a i t) * poisson (y i t)) ≤
        ∑ i, ∑ j, ((logWeight n (a i t) + logWeight n (a j t)) / 2) * poisson (z i j t) at h
      let w (i : Fin n) := logWeight n (a i t)
      let m (i j : Fin n) := (w i + w j) / 2
      have hLeft : (∑ i : Fin n, ∑ _ : Fin n, w i) = (n : ℝ) * ∑ i, w i := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [mul_sum]
      have hRight : (∑ _ : Fin n, ∑ j : Fin n, w j) = (n : ℝ) * ∑ j, w j := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hconst : (∑ i, ∑ j, m i j) = (n : ℝ) * ∑ i, w i := by
        simp only [m, ← Finset.sum_div, sum_add_distrib]
        rw [hLeft, hRight]
        ring
      have h₁ : (∑ i, (n * w i) * (poisson (y i t) - 1) / 2) =
          (1 / 2) * ((n : ℝ) * (∑ i, w i * poisson (y i t)) - n * (∑ i, w i)) := by
        calc
          _ = ∑ i, (1 / 2) * ((n : ℝ) * (w i * poisson (y i t)) - n * w i) :=
            sum_congr rfl fun _ _ => by ring
          _ = _ := by simp only [← mul_sum, sum_sub_distrib]
      have h₂ : (∑ i, ∑ j, m i j * (poisson (z i j t) - 1) / 2) =
          (1 / 2) * ((∑ i, ∑ j, m i j * poisson (z i j t)) - (∑ i, ∑ j, m i j)) := by
        calc
          _ = ∑ i, ∑ j, (1 / 2) * (m i j * poisson (z i j t) - m i j) :=
            sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
          _ = _ := by simp only [← mul_sum, sum_sub_distrib]
      change (∑ i, (n * w i) * (poisson (y i t) - 1) / 2) -
        (∑ i, ∑ j, m i j * (poisson (z i j t) - 1) / 2) ≤ 0
      rw [h₁, h₂, hconst]
      change (n : ℝ) * (∑ i, w i * poisson (y i t)) ≤
        ∑ i, ∑ j, m i j * poisson (z i j t) at h
      linarith only [h]
  have hloglim {F : ℝ → ℂ} (hF : Tendsto F atTop (𝓝 0)) :
      Tendsto (fun t => Real.log ‖1 - F t‖) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun t => ‖(1 : ℂ) - F t‖) atTop (𝓝 1) := by
      simpa only [sub_zero, norm_one] using ((tendsto_const_nhds (x := (1 : ℂ))).sub hF).norm
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp h₁
    change Tendsto (fun t => Real.log ‖1 - F t‖) atTop (𝓝 (Real.log 1)) at h
    simpa only [Real.log_one] using h
  have hy (i : Fin n) : Tendsto (y i) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp ((a_lim i).const_mul_atTop hnr))
    have h' := (Complex.continuous_ofReal.tendsto 0).comp h
    change Tendsto (y i) atTop (𝓝 ((0 : ℝ) : ℂ)) at h'
    simpa only [Complex.ofReal_zero] using h'
  have hz (i j : Fin n) : Tendsto (z i j) atTop (𝓝 0) := by
    have hm : Tendsto (fun t => midpoint (a i t) (a j t)) atTop atTop := by
      apply tendsto_atTop.mpr
      intro B
      filter_upwards [tendsto_atTop.mp (a_lim i) (2 * B), tendsto_atTop.mp (a_lim j) 0] with _ hi hj
      unfold midpoint
      linarith
    have hh := (Complex.continuous_ofReal.tendsto 0).comp
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hm))
    simpa only [z, Function.comp_apply, Complex.ofReal_zero, zero_mul] using hh.mul_const (C i j)
  have hQ : Tendsto Q atTop (𝓝 0) := by
    simpa [Q] using (tendsto_finsetSum univ fun i _ => hloglim (hy i)).sub
      (tendsto_finsetSum univ fun i _ => tendsto_finsetSum univ fun j _ => hloglim (hz i j))
  have hQ0 : 0 ≤ Q 0 := le_of_tendsto hQ <|
    (eventually_ge_atTop (0 : ℝ)).mono fun t ht => hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have iz (i j : Fin n) : z i j 0 = A i j := by simp only [z, a_zero, hback]
  have iy (i : Fin n) : y i 0 = A i i ^ n := by
    change (Real.exp (-(n * a i 0)) : ℂ) = A i i ^ n
    rw [a_zero, ← mul_neg, Real.exp_nat_mul, he₀, Complex.ofReal_pow, ← diag_real hA i]
  have hz0 (i j : Fin n) : ‖1 - A i j‖ ≠ 0 := by
    have h := exp_entry_norm_lt (show 0 < midpoint (a₀ i) (a₀ j) by
      unfold midpoint; linarith [ha₀ i, ha₀ j]) (hCnorm i j)
    rw [hback] at h
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun he => h.ne (by rw [← he, norm_one]))
  have hy0 (i : Fin n) : ‖1 - A i i ^ n‖ ≠ 0 := by
    have h := exp_entry_norm_lt (mul_pos hnr (ha₀ i)) (z := (1 : ℂ)) (le_of_eq norm_one)
    rw [mul_one, ← a_zero i] at h
    change ‖y i 0‖ < 1 at h
    rw [iy] at h
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun he => h.ne (by rw [← he, norm_one]))
  apply from_full_strict_diagonal A hA hdiag
  apply (Real.log_le_log_iff
    (prod_pos fun i _ => prod_pos fun j _ => lt_of_le_of_ne (norm_nonneg _) (hz0 i j).symm)
    (prod_pos fun i _ => lt_of_le_of_ne (norm_nonneg _) (hy0 i).symm)).mp
  rw [Real.log_prod (fun i _ => prod_ne_zero_iff.mpr (fun j _ => hz0 i j)),
    Real.log_prod (fun i _ => hy0 i)]
  simp_rw [Real.log_prod (fun j _ => hz0 _ j)]
  simpa only [Q, iz, iy, sub_nonneg] using hQ0

/-- Section 2. The scalar minorant implies the cancelled matrix bound by the
backward radial flow. Positive diagonal approximants handle zero radii. -/
theorem radial_flow_from_minorant {n : ℕ} (hn : 3 ≤ n) (kernel : KernelBound n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (hdiag : ∀ i : Fin n, (A i i).re < 1) : Cancelled A := by
  let B (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
    (1 - t) • A + (t / 2) • (1 : Matrix (Fin n) (Fin n) ℂ)
  have hB0 : B 0 = A := by simp [B]
  have hBn (t : ℝ) (ht : t ∈ Set.Ioo 0 1) : (B t).PosSemidef :=
    (hA.smul (sub_nonneg.mpr ht.2.le)).add
      (Matrix.PosSemidef.one.smul (div_nonneg ht.1.le (by norm_num)))
  have hBd (i : Fin n) (t : ℝ) : (B t i i).re = (1 - t) * (A i i).re + t / 2 := by
    simp [B, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, Complex.mul_re]
  let F (t : ℝ) := ∏ i : Fin n, ∏ j : Fin n, ‖1 - B t i j‖
  let G (t : ℝ) := ∏ i : Fin n, ‖1 - B t i i ^ n‖
  have hc (i j : Fin n) : Continuous (fun t => B t i j) := by
    simp only [B, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    fun_prop
  have hFc : Continuous F := continuous_finsetProd _ fun i _ =>
    continuous_finsetProd _ fun j _ => (continuous_const.sub (hc i j)).norm
  have hGc : Continuous G := continuous_finsetProd _ fun i _ =>
    (continuous_const.sub ((hc i i).pow n)).norm
  have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 1 :=
    Ioo_mem_nhdsGT (by norm_num)
  have hle : F 0 ≤ G 0 := le_of_tendsto_of_tendsto
    hFc.continuousAt.continuousWithinAt hGc.continuousAt.continuousWithinAt <|
    ht.mono fun t ht' => by
      have hpos (i : Fin n) : 0 < (B t i i).re := by
        rw [hBd]
        have h := mul_nonneg (sub_nonneg.mpr ht'.2.le) (diag_re_nonneg hA i)
        linarith [ht'.1]
      have htr (i : Fin n) : (B t i i).re < 1 := by
        rw [hBd]
        have h := mul_lt_mul_of_pos_left (hdiag i) (sub_pos.mpr ht'.2)
        linarith [ht'.1]
      exact of_cancelled (hBn t ht') (radial_flow_positive hn kernel (B t) (hBn t ht') hpos htr)
  apply from_full_strict_diagonal A hA hdiag
  simpa only [F, G, hB0] using hle

/-! ## Assembly -/

private lemma interior_weights (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (m : ℕ) (hm : 3 ≤ m) :
    0 ≤ fejerWeight (radii a b) (Real.cosh (midpoint a b)) m := by
  have hc : 0 < midpoint a b := by unfold midpoint; positivity
  have hm' : 3 ≤ (m : ℝ) := by exact_mod_cast hm
  have integral_sign :
      0 ≤ ∫ u in (-1 : ℝ)..1, triangular u *
        (∫ v in (-1 : ℝ)..1, green (midpoint a b) v * differential a b ((m : ℝ) + u + v)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    refine mul_nonneg (sub_nonneg.mpr (abs_le.mpr hu)) ?_
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro v hv
    have hg : 0 ≤ green (midpoint a b) v := by
      unfold green
      exact div_nonneg (Real.sinh_nonneg_iff.mpr
        (mul_nonneg hc.le (sub_nonneg.mpr (abs_le.mpr hv)))) hc.le
    exact mul_nonneg hg (differential_nonneg a b _ ha hb (by
      have hu' := hu.1
      have hv' := hv.1
      linarith))
  rw [← green_kernel_identity a b ha hb m hm] at integral_sign
  linarith

/-- The finite sum of squares assembles the scalar kernel estimate. -/
theorem kernel_bound (n : ℕ) (hn : 3 ≤ n) : KernelBound n := by
  intro a b ha hb z hz
  have endBounds := hyperbolic_endpoint_bounds n hn a b ha hb
  have h0 : radii a b 0 = 0 := by simp [radii, radialU, H]
  have h1 : radii a b 1 = 0 := by simp [radii, radialU, H]
  rw [fourier_sos _ _ _ hn h0 h1 z hz]
  refine add_nonneg endBounds.1 (sum_nonneg fun j _ => mul_nonneg ?_ (sq_nonneg _))
  by_cases hj : j < 3
  · exact endBounds.2 j hj
  · exact interior_weights a b ha hb j (by omega)

end PsdProduct

open PsdProduct

/-- Saigyukari's Theorem 1. The empty-order statement also holds. -/
theorem psd_product_inequality {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) :
    (∏ i : Fin n, ∏ j : Fin n, ‖1 - A i j‖) ≤ ∏ i : Fin n, ‖1 - A i i ^ n‖ := by
  by_cases h0 : n = 0
  · subst n
    simp
  by_cases h1 : n = 1
  · subst n
    simp
  by_cases h2 : n = 2
  · subst n
    exact of_cancelled hA (order_two A hA)
  have hn : 3 ≤ n := by omega
  by_cases hunit : ∃ i : Fin n, (A i i).re = 1
  · obtain ⟨i, hi⟩ := hunit
    have hentry : A i i = 1 := by simpa [hi] using diag_real hA i
    have hrow : (∏ j : Fin n, ‖1 - A i j‖) = 0 :=
      prod_eq_zero (mem_univ i) (by simp [hentry])
    rw [prod_eq_zero (mem_univ i) hrow]
    exact prod_nonneg fun _ _ => norm_nonneg _
  · have hdiag : ∀ i : Fin n, (A i i).re ≠ 1 := fun i hi => hunit ⟨i, hi⟩
    apply of_cancelled hA
    apply cancelled_of_normalize hA
    exact radial_flow_from_minorant hn (kernel_bound n hn) _ (normalize_psd hA)
      (normalize_lt_one hdiag)

set_option pp.fullNames true in
#print axioms psd_product_inequality
