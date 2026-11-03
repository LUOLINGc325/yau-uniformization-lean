import Yau.Proofs.G01KahlerWirtinger

noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
set_option backward.isDefEq.respectTransparency false
open Yau Yau.LeafProofs
variable {n r : ℕ}

def matrixWirt (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (k : Fin n) : Matrix (Fin r) (Fin r) ℂ :=
  fun a b => wirt (fun w => H w a b) z (stdVec k)

def matrixWirtBar (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (k : Fin n) : Matrix (Fin r) (Fin r) ℂ :=
  fun a b => wirtBar (fun w => H w a b) z (stdVec k)

theorem matrixWirt_mul (A B : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (hA : ∀ a b, DifferentiableAt ℝ (fun w => A w a b) z)
    (hB : ∀ a b, DifferentiableAt ℝ (fun w => B w a b) z) (k : Fin n) :
    matrixWirt (fun w => A w * B w) z k =
      matrixWirt A z k * B z + A z * matrixWirt B z k := by
  ext a b
  change wirt (fun w => ∑ c, A w a c * B w c b) z (stdVec k) = _
  rw [L14Aux.wirt_sum_fun Finset.univ (fun c w => A w a c * B w c b) z (stdVec k)
    (fun c _ => (hA a c).mul (hB c b))]
  simp_rw [L14Aux.wirt_mul_rule _ _ z (stdVec k) (hA a _) (hB _ b)]
  simp only [Matrix.add_apply, Matrix.mul_apply, matrixWirt, Finset.sum_add_distrib]

theorem matrixWirtBar_mul (A B : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (hA : ∀ a b, DifferentiableAt ℝ (fun w => A w a b) z)
    (hB : ∀ a b, DifferentiableAt ℝ (fun w => B w a b) z) (k : Fin n) :
    matrixWirtBar (fun w => A w * B w) z k =
      matrixWirtBar A z k * B z + A z * matrixWirtBar B z k := by
  ext a b
  change wirtBar (fun w => ∑ c, A w a c * B w c b) z (stdVec k) = _
  rw [L14Aux.wirtBar_sum_fun Finset.univ (fun c w => A w a c * B w c b) z (stdVec k)
    (fun c _ => (hA a c).mul (hB c b))]
  simp_rw [L14Aux.wirtBar_mul_rule _ _ z (stdVec k) (hA a _) (hB _ b)]
  simp only [Matrix.add_apply, Matrix.mul_apply, matrixWirtBar, Finset.sum_add_distrib]

theorem wirt_wirt_comm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f : X → ℂ) (z : X) (hf : ContDiffAt ℝ 2 f z) (v w : X) :
    wirt (fun y => wirt f y v) z w = wirt (fun y => wirt f y w) z v := by
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [wirt, L14Aux.fderiv_wirt hd, L14Aux.fderiv_wirt hd,
    wirt, L14Aux.fderiv_wirt hd, L14Aux.fderiv_wirt hd]
  rw [hs w v, hs (Complex.I • w) v, hs w (Complex.I • v),
    hs (Complex.I • w) (Complex.I • v)]
  ring

variable {M : ComplexManifold n}

def chernA (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (k : Fin n) :=
  BundleDbar.chernConnectionMatrix (hMat h x) z k

def chernF (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (k l : Fin n) :=
  -matrixWirtBar (fun w => chernA h x w k) z l

def chernInChart (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (i j k l : Fin n) : ℂ :=
  -wirt (fun w => wirtBar (fun t => hMat h x t j i) w (stdVec l)) z (stdVec k) +
    ∑ p, ∑ q, (hMat h x z)⁻¹ p q *
      wirt (fun t => hMat h x t q i) z (stdVec k) *
      wirtBar (fun t => hMat h x t j p) z (stdVec l)

theorem chernA_contDiffOn (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) (k a b : Fin n) :
    ContDiffOn ℝ ∞ (fun z => chernA h x z k a b) (chartTarget x) :=
  L14Aux.chernConnectionMatrix_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) x)
    (hMat h x) (L17Aux.hMat_contDiffOn_of_metricSmooth h hs x)
    (fun z hz => ((L12Aux.hMat_posDef h x z hz).isUnit.map Matrix.detMonoidHom).ne_zero) k a b

theorem chernA_lower (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (k : Fin n) :
    hMat h x z * chernA h x z k = matrixWirt (hMat h x) z k :=
  L14Aux.chernConnection_lower (hMat h x) z
    ((L12Aux.hMat_posDef h x z hz).isUnit.map Matrix.detMonoidHom) k

theorem chernA_torsion_symm (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (k i p : Fin n) :
    chernA h x z k p i = chernA h x z i p k := by
  simp only [chernA, BundleDbar.chernConnectionMatrix, Matrix.mul_apply, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [kahler_hMat_wirt_symm h hs hk x z hz k i q]

theorem chernInChart_center (h : HermitianField M) (x : M.Carrier) (i j k l : Fin n) :
    chernInChart h x (chartPt x x) i j k l = chernCurvature h x i j k l := rfl

end Yau.NodeProofs.G01Aux
