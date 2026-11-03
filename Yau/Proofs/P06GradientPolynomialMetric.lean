import Yau.Proofs.P06WeitzenbockEndomorphism
import Yau.Proofs.P06WeitzenbockNaturality

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux.GradientPoly
open Yau Yau.LeafProofs G04Aux L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

/-- Recover the Hermitian coefficient matrix from the real alternating
matrix, with the same factor two as the original iota map. -/
def twoHermitianMatrix (U : Matrix (RIdx n) (RIdx n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ((U (i,0) (j,1) : ℂ) + Complex.I * (U (i,0) (j,0) : ℂ)) / 2

theorem twoHermitianMatrix_raw (U : Matrix (RIdx n) (RIdx n) ℝ)
    (hJ : ∀ b d, U (jIndex n b) (jIndex n d) = jSign b * jSign d * U b d) :
    U = (-2 : ℝ) • (G01Aux.rawReal (twoHermitianMatrix U) * jMatrix n) := by
  have h11 (i j : Fin n) : U (i,1) (j,1) = U (i,0) (j,0) := by
    simpa [jIndex, jSign] using hJ (i,0) (j,0)
  have h10 (i j : Fin n) : U (i,1) (j,0) = -U (i,0) (j,1) := by
    simpa [jIndex, jSign] using hJ (i,0) (j,1)
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.smul_apply, mul_jMatrix, G01Aux.rawReal,
      twoHermitianMatrix, jIndex, jSign, h11, h10] <;> ring

theorem twoHermitianMatrix_hermitian (U : Matrix (RIdx n) (RIdx n) ℝ)
    (hsk : ∀ b d, U d b = -U b d)
    (hJ : ∀ b d, U (jIndex n b) (jIndex n d) = jSign b * jSign d * U b d) :
    (twoHermitianMatrix U).IsHermitian := by
  have h10 (i j : Fin n) : U (i,1) (j,0) = -U (i,0) (j,1) := by
    simpa [jIndex, jSign] using hJ (i,0) (j,1)
  have h01 (i j : Fin n) : U (j,0) (i,1) = U (i,0) (j,1) := by
    rw [hsk, h10]; ring
  ext i j
  apply Complex.ext <;>
    simp [Matrix.conjTranspose_apply, twoHermitianMatrix, h01 i j, hsk (i,0) (j,0)]

def covariantHermitianMatrix (h : HermitianField M) (A : RealForm M 2)
    (c : M.Carrier) (z : ComplexVector n) (a : RIdx n) : Matrix (Fin n) (Fin n) ℂ :=
  twoHermitianMatrix (P06Weitzenbock.covariantTwoMatrix h A c z a)

theorem covariantHermitianMatrix_hermitian (g : SmoothMetric M) (hK : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a : RIdx n) :
    (covariantHermitianMatrix g.form A c z a).IsHermitian := by
  exact twoHermitianMatrix_hermitian _
    (covariantTwo_skew g.form A hA c hz a)
    (covariantTwo_J g.form (metricSmooth_of_smoothMetric g) hK A hA h11 c hz a)

theorem covariantTwoMatrix_eq_raw (g : SmoothMetric M) (hK : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a : RIdx n) :
    P06Weitzenbock.covariantTwoMatrix g.form A c z a =
      (-2 : ℝ) • (G01Aux.rawReal (covariantHermitianMatrix g.form A c z a) * jMatrix n) :=
  twoHermitianMatrix_raw _
    (covariantTwo_J g.form (metricSmooth_of_smoothMetric g) hK A hA h11 c hz a)

theorem coefficientPairing_two_trace (G U V : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.IsSymm) (hV : ∀ b d, V d b = -V b d) :
    L03.tensorCoefficientPairing G (fun I : Fin 2 → RIdx n => U (I 0) (I 1))
      (fun I : Fin 2 → RIdx n => V (I 0) (I 1)) =
        -Matrix.trace (G * U * G * V) := by
  rw [← alternating_contraction_trace G U V hG hV]
  simp only [L03.tensorCoefficientPairing, L23Aux.sum_tensor_cons,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.cons_zero, Fin.cons_one, Fin.cons_succ,
    Fintype.sum_unique, mul_one]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem raw_two_pairing (H C D : Matrix (Fin n) (Fin n) ℂ) :
    -(1 / 2 : ℝ) * Matrix.trace
      (((1 / 2 : ℝ) • G01Aux.rawReal H) *
        ((-2 : ℝ) • (G01Aux.rawReal C * jMatrix n)) *
        ((1 / 2 : ℝ) • G01Aux.rawReal H) *
        ((-2 : ℝ) • (G01Aux.rawReal D * jMatrix n))) =
      (Matrix.trace (H * C * H * D)).re := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num only [show (1 / 2 : ℝ) * (-2) * (1 / 2) * (-2) = 1 by norm_num,
    one_smul]
  have hp : G01Aux.rawReal H * (G01Aux.rawReal C * jMatrix n) *
      G01Aux.rawReal H * (G01Aux.rawReal D * jMatrix n) =
      -G01Aux.rawReal (H * C * H * D) := by
    calc
      _ = G01Aux.rawReal H * G01Aux.rawReal C *
          (jMatrix n * G01Aux.rawReal H) * G01Aux.rawReal D * jMatrix n := by noncomm_ring
      _ = G01Aux.rawReal H * G01Aux.rawReal C *
          (G01Aux.rawReal H * jMatrix n) * G01Aux.rawReal D * jMatrix n := by
            rw [rawReal_commute_J]
      _ = G01Aux.rawReal H * G01Aux.rawReal C * G01Aux.rawReal H *
          (jMatrix n * G01Aux.rawReal D) * jMatrix n := by noncomm_ring
      _ = G01Aux.rawReal H * G01Aux.rawReal C * G01Aux.rawReal H *
          (G01Aux.rawReal D * jMatrix n) * jMatrix n := by rw [rawReal_commute_J]
      _ = -(G01Aux.rawReal H * G01Aux.rawReal C * G01Aux.rawReal H *
          G01Aux.rawReal D) := by
        simp only [Matrix.mul_assoc, jMatrix_sq, Matrix.mul_neg, Matrix.mul_one]
      _ = _ := by simp only [G01Aux.rawReal_mul]
  rw [hp, Matrix.trace_neg, G01Aux.rawReal_trace]
  ring

/-- The original factor 1/2! leaves exactly the complex relative trace
pairing for every pair of actual covariant derivative directions. -/
theorem covariant_pairing_eq_trace (g : SmoothMetric M) (hK : IsKahler g)
    (A B : RealForm M 2) (hA : SmoothRealForm A) (hB : SmoothRealForm B)
    (h11A : RealOneOne A) (h11B : RealOneOne B)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a b : RIdx n) :
    (1 / 2 : ℝ) * L03.tensorCoefficientPairing (realMetricFn g.form c z)⁻¹
      (fun I => covariantComponents g.form c (formComponents A c) z a I)
      (fun I => covariantComponents g.form c (formComponents B c) z b I) =
      (Matrix.trace ((hMat g.form c z)⁻¹ * covariantHermitianMatrix g.form A c z a *
        (hMat g.form c z)⁻¹ * covariantHermitianMatrix g.form B c z b)).re := by
  have hI (U : RealForm M 2) (s : RIdx n) :
      (fun I => covariantComponents g.form c (formComponents U c) z s I) =
      (fun I : Fin 2 → RIdx n => P06Weitzenbock.covariantTwoMatrix g.form U c z s (I 0) (I 1)) := by
    funext I
    have he : I = ![I 0,I 1] := by funext i; fin_cases i <;> rfl
    rw [he]
    rfl
  have hV : ∀ d e, P06Weitzenbock.covariantTwoMatrix g.form B c z b e d =
      -P06Weitzenbock.covariantTwoMatrix g.form B c z b d e :=
    covariantTwo_skew g.form B hB c hz b
  rw [hI A a, hI B b, coefficientPairing_two_trace _
    (P06Weitzenbock.covariantTwoMatrix g.form A c z a)
    (P06Weitzenbock.covariantTwoMatrix g.form B c z b)
    (L12Aux.realMetricFn_isSymm g.form c z).inv hV,
    covariantTwoMatrix_eq_raw g hK A hA h11A c hz a,
    covariantTwoMatrix_eq_raw g hK B hB h11B c hz b,
    G01Aux.realMetricFn_inverse_eq g.form c z hz]
  convert raw_two_pairing ((hMat g.form c z)⁻¹)
    (covariantHermitianMatrix g.form A c z a) (covariantHermitianMatrix g.form B c z b) using 1 <;> ring

end Yau.NodeProofs.P06Aux.GradientPoly
