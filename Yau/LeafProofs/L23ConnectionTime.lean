import Yau.LeafProofs.L23RicciDerivative

/-! Time variation of the original Christoffel symbols, obtained by
differentiating their actual lowered Koszul identity. -/

noncomputable section
open Filter
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem christoffel_time_differentiableAt
    (h : ℝ → HermitianField M) (a b : ℝ) (hh : MetricFamilySmooth h (Set.Icc a b))
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (l i j : RIdx n) :
    DifferentiableAt ℝ (fun s => christoffel (h s) c z l i j) t := by
  have hJ : ContDiffAt ℝ ∞ (fun u : ComplexVector n × ℝ =>
      christoffel (h u.2) c u.1 l i j) (z,t) :=
    (christoffelFamilySmooth_joint h a b hh c l i j).contDiffAt
    ((isOpen_flowChartDomain c a b).mem_nhds ⟨hz,ht⟩)
  have hs := hJ.comp t (contDiffAt_const.prodMk contDiffAt_id)
  exact hs.differentiableAt (by simp)

theorem localRealRicciFlow_loweredChristoffel_time
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hx : chartInv c z ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b) (i j q : RIdx n) :
    (∑ l, deriv (fun s => christoffel (h s) c z l i j) t*realMetricFn (h t) c z l q)=
      -(σ/2)*(covariantD (h t) c (ricciTensor (h t) c) z ![i,j,q]+
        covariantD (h t) c (ricciTensor (h t) c) z ![j,i,q]-
          covariantD (h t) c (ricciTensor (h t) c) z ![q,i,j]) := by
  have hdL := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    (christoffel_time_differentiableAt h a b hflow.1 c hz t ht l i j).hasDerivAt.mul
      (localRealRicciFlow_metric_hasDerivAt_inChart h O a b σ hflow c hz hx t ht l q))
  have hdR := (((localRealRicciFlow_rDeriv_metric_hasDerivAt_inChart h O a b σ hO
    hflow c hz hx t ht i j q).add
      (localRealRicciFlow_rDeriv_metric_hasDerivAt_inChart h O a b σ hO
        hflow c hz hx t ht j i q)).sub
          (localRealRicciFlow_rDeriv_metric_hasDerivAt_inChart h O a b σ hO
            hflow c hz hx t ht q i j)).div_const 2
  have heq : (fun s => ∑ l, christoffel (h s) c z l i j*realMetricFn (h s) c z l q)=ᶠ[𝓝 t]
      (fun s => (rDeriv (fun w => realMetricFn (h s) c w j q) z i+
        rDeriv (fun w => realMetricFn (h s) c w i q) z j-
          rDeriv (fun w => realMetricFn (h s) c w i j) z q)/2) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact christoffel_metric_contraction (h s) (metricFamilySmooth_slice h hflow.1 hs) c z hz i j q
  have hderiv := hdL.unique (hdR.congr_of_eventuallyEq heq)
  have hS : (∑ l, (deriv (fun s => christoffel (h s) c z l i j) t*realMetricFn (h t) c z l q+
      christoffel (h t) c z l i j*(-σ*realRicciCoeff (h t) c z l q)))=
      (∑ l, deriv (fun s => christoffel (h s) c z l i j) t*realMetricFn (h t) c z l q)-
        σ*∑ l, christoffel (h t) c z l i j*realRicciCoeff (h t) c z l q := by
    calc
      _=∑ l, (deriv (fun s => christoffel (h s) c z l i j) t*realMetricFn (h t) c z l q-
          σ*(christoffel (h t) c z l i j*realRicciCoeff (h t) c z l q)) := by
        apply Finset.sum_congr rfl
        intro l _
        ring
      _=_ := by rw [Finset.sum_sub_distrib,←Finset.mul_sum]
  rw [hS] at hderiv
  rw [ricciDerivative_koszul_combination (h t)
    (metricFamilySmooth_slice h hflow.1 ⟨ht.1.le,ht.2.le⟩) c hz]
  nlinarith [hderiv]

theorem localRealRicciFlow_christoffel_hasDerivAt_inChart
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hx : chartInv c z ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b) (p i j : RIdx n) :
    HasDerivAt (fun s => christoffel (h s) c z p i j)
      (-(σ/2)*∑ q, (realMetricFn (h t) c z)⁻¹ p q*
        (covariantD (h t) c (ricciTensor (h t) c) z ![i,j,q]+
          covariantD (h t) c (ricciTensor (h t) c) z ![j,i,q]-
            covariantD (h t) c (ricciTensor (h t) c) z ![q,i,j])) t := by
  let G := realMetricFn (h t) c z
  let V : RIdx n → ℝ := fun l => deriv (fun s => christoffel (h s) c z l i j) t
  let C : RIdx n → ℝ := fun q =>
    covariantD (h t) c (ricciTensor (h t) c) z ![i,j,q]+
      covariantD (h t) c (ricciTensor (h t) c) z ![j,i,q]-
        covariantD (h t) c (ricciTensor (h t) c) z ![q,i,j]
  have hGV : G*ᵥV=fun q => -(σ/2)*C q := by
    funext q
    have hlow := localRealRicciFlow_loweredChristoffel_time h O a b σ hO
      hflow c hz hx t ht i j q
    change (∑ l, G q l*V l)=_
    rw [show (∑ l, G q l*V l)=(∑ l, V l*G l q) by
      apply Finset.sum_congr rfl
      intro l _
      dsimp only [G]
      rw [L12Aux.realMetricFn_symm (h t) c z q l]
      ring]
    exact hlow
  have hInv : G⁻¹*G=1 := Matrix.nonsing_inv_mul G
    (isUnit_iff_ne_zero.mpr (L12Aux.realMetricFn_posDef (h t) c z hz).det_pos.ne')
  have hv : V=G⁻¹*ᵥ(fun q => -(σ/2)*C q) := by
    rw [←hGV,Matrix.mulVec_mulVec,hInv,Matrix.one_mulVec]
  have hval := congrFun hv p
  have hd := (christoffel_time_differentiableAt h a b hflow.1 c hz t ht p i j).hasDerivAt
  change HasDerivAt (fun s => christoffel (h s) c z p i j) (V p) t at hd
  rw [hval] at hd
  convert hd using 1
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

end Yau.LeafProofs.L23Aux
