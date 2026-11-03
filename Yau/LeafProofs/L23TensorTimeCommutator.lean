import Yau.LeafProofs.L23CurvatureTime

/-! The actual time/connection commutator on every covariant slot. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {M : ComplexManifold n}

def tensorTimeDerivative (A : ℝ → ComplexVector n → CovTensor n r) (t : ℝ)
    (z : ComplexVector n) : CovTensor n r := fun v => deriv (fun s => A s z v) t

theorem covariantDFamily_hasDerivAt
    (h : ℝ → HermitianField M) (a b : ℝ) (hh : MetricFamilySmooth h (Set.Icc a b))
    (c : M.Carrier) (A : ℝ → ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => A p.2 p.1 v)
      (flowChartDomain c a b))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (i : RIdx n) (v : Fin r → RIdx n) :
    HasDerivAt (fun s => covariantD (h s) c (A s) z (Fin.cons i v))
      (covariantD (h t) c (tensorTimeDerivative A t) z (Fin.cons i v)-
        ∑ j : Fin r, ∑ p, dotChristoffel h c z t p i (v j)*A t z (Function.update v j p)) t := by
  have hAd (u : Fin r → RIdx n) : DifferentiableAt ℝ (fun s => A s z u) t := by
    have hJ : ContDiffAt ℝ ∞ (fun p : ComplexVector n × ℝ => A p.2 p.1 u) (z,t) :=
      (hA u).contDiffAt ((isOpen_flowChartDomain c a b).mem_nhds ⟨hz,ht⟩)
    exact (hJ.comp t (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hJ : ContDiffAt ℝ 2 (fun p : ComplexVector n × ℝ => A p.2 p.1 v) (z,t) :=
    ((hA v).contDiffAt ((isOpen_flowChartDomain c a b).mem_nhds ⟨hz,ht⟩)).of_le (by simp)
  have hpartial := joint_spatial_time_hasDerivAt
    (fun p : ComplexVector n × ℝ => A p.2 p.1 v) z t hJ i
  have hΓ (j : Fin r) (p : RIdx n) :
      HasDerivAt (fun s => christoffel (h s) c z p i (v j))
        (dotChristoffel h c z t p i (v j)) t :=
    (christoffel_time_differentiableAt h a b hh c hz t ht p i (v j)).hasDerivAt
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun p _ =>
      (hΓ j p).mul (hAd (Function.update v j p)).hasDerivAt))
  have hd := hpartial.sub hsum
  convert hd using 1
  · funext s
    rw [covariantD_cons]
    rfl
  · simp only [covariantD_cons,tensorConnectionAction,tensorSlotAction,
      L12Aux.connectionMatrix,tensorTimeDerivative,Finset.sum_add_distrib]
    ring

end Yau.LeafProofs.L23Aux
