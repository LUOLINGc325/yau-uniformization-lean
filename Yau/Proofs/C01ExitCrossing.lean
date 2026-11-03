import Yau.Proofs.C01ExitSphere

/-! Every true path to the exterior of an original distance sphere
crosses that sphere. Restricting its actual extended length gives the
first-exit lower bound, with no minimizing geodesic assumption. -/

noncomputable section

open scoped Manifold Topology ContDiff ENNReal

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem exitDistanceProfile_le_distance_outside
    (g : SmoothMetric M) (k : HermitianField M) (hk : MetricSmooth k)
    (o : M.Carrier) (L : ℝ) (hL : 0 ≤ L) (x : M.Carrier)
    (hx : L ≤ inducedDistance g.form o x) :
    exitDistanceProfile g k o L ≤ inducedDistance k o x := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup k z
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨f, hf₀, hf₁, hf, _hv, hlen⟩ := exists_smooth_nearMinimizingPath k hk o x ε hε
  have hdist : Continuous (fun s => inducedDistance g.form o (f s)) :=
    ((Yau.LeafProofs.L12Aux.continuous_inducedDistance g).comp
      (continuous_const.prodMk continuous_id)).comp hf.continuous
  have hbetween : L ∈ Set.Icc (inducedDistance g.form o (f 0))
      (inducedDistance g.form o (f 1)) := by
    rw [hf₀, hf₁, g.induced_distance_eq_zero.mpr rfl]
    exact ⟨hL, hx⟩
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc zero_le_one hdist.continuousOn hbetween
  have hboundary : f u ∈ initialDistanceSphere g o L := hfu
  have hmin := exitDistanceProfile_le g k hk o L hL (f u) hboundary
  have hsegment := riemannianEDist_le_pathELength_of_contMDiffAt_Ioo k hk hu.1
    hf.continuous.continuousOn (fun s _ => hf.contMDiffAt)
  rw [hf₀] at hsegment
  let γ := integrableCurve_of_contMDiff k hk hf
  have hE : ENNReal.ofReal (exitDistanceProfile g k o L) ≤ ENNReal.ofReal (curveLength k γ.1) := by
    calc
      _ ≤ ENNReal.ofReal (inducedDistance k o (f u)) := ENNReal.ofReal_le_ofReal hmin
      _ = Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) o (f u) :=
        inducedDistance_eq_riemannianEDist k hk o (f u)
      _ ≤ Manifold.pathELength 𝓘(ℝ, ComplexVector n) f 0 u := hsegment
      _ ≤ Manifold.pathELength 𝓘(ℝ, ComplexVector n) f 0 1 :=
        Manifold.pathELength_mono le_rfl hu.2
      _ = _ := (curveLength_eq_pathELength k γ).symm
  have hreal := (ENNReal.ofReal_le_ofReal_iff (curveLength_nonneg k γ.1)).mp hE
  exact hreal.trans_lt hlen

end Yau.NodeProofs.C01Aux
