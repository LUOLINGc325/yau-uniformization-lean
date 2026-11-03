import spec.CHAIN.CONTRACTS

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder InnerProductSpace
open Bundle

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual flat coefficient line in the paper; this is not a frame of K_M. -/
abbrev CanonicalCoefficients (M : ComplexManifold n) :=
  Bundle.Trivial M.Carrier (ComplexVector 1)

theorem canonicalCoefficients_eq :
    CanonicalCoefficients M = BundleDbar.TrivialLineFiber M := rfl

theorem coefficient_holomorphic :
    BundleDbar.Holomorphic (r := 1) (CanonicalCoefficients M) := by
  change ContMDiffVectorBundle ⊤ (ComplexVector 1) (CanonicalCoefficients M) (ComplexModel n)
  infer_instance

def flatMetric : BundleDbar.Metric (CanonicalCoefficients M) := fun _ =>
  { toFun := fun u v => ⟪u,v⟫_ℂ
    map_add_left := inner_add_left
    map_smul_left := fun c u v => inner_smul_left u v c
    map_add_right := inner_add_right
    map_smul_right := fun c u v => by rw [inner_smul_right,mul_comm]
    conjugate_symmetric := fun u v => (inner_conj_symm u v).symm
    self_adjoint := fun u => inner_self_im (𝕜 := ℂ) u
    positive_definite := fun u => by
      have hn : (⟪u,u⟫_ℂ).re = ‖u‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
      rw [hn]
      exact ⟨sq_nonneg _,sq_eq_zero_iff.trans norm_eq_zero⟩ }

theorem flatMetric_apply (x : M.Carrier) (u v : ComplexVector 1) :
    (flatMetric (M := M) x).toFun u v = ⟪u,v⟫_ℂ := rfl

theorem coefficient_localTriv (a : M.Carrier) :
    BundleDbar.localTriv (r := 1) (CanonicalCoefficients M) a =
      Bundle.Trivial.trivialization M.Carrier (ComplexVector 1) := rfl

theorem coefficient_localDomain (a : M.Carrier) :
    BundleDbar.localDomain (r := 1) (CanonicalCoefficients M) a = chartTarget a := by
  simp only [BundleDbar.localDomain, coefficient_localTriv,
    Bundle.Trivial.trivialization_baseSet, Set.preimage_univ, Set.inter_univ]

theorem flat_metricMatrix (a : M.Carrier) (z : ComplexVector n) :
    BundleDbar.metricMatrix (r := 1) (CanonicalCoefficients M) flatMetric a z = 1 := by
  ext α β
  fin_cases α
  fin_cases β
  simp [BundleDbar.metricMatrix,coefficient_localTriv,flatMetric,stdVec]

theorem flatMetric_smooth :
    BundleDbar.SmoothMetric (r := 1) (CanonicalCoefficients M) flatMetric := by
  intro a α β
  simp only [flat_metricMatrix]
  exact contDiffOn_const

theorem flat_curvature (a : M.Carrier) (z : ComplexVector n) (i j : Fin n) :
    BundleDbar.curvature (r := 1) (CanonicalCoefficients M) flatMetric a z i j = 0 := by
  ext α β
  simp [BundleDbar.curvature,flat_metricMatrix,BundleDbar.curvatureMatrix,
    BundleDbar.chernConnectionMatrix,wirt,wirtBar]

end Yau.Proofs.P04Aux
