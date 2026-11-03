import Yau.Proofs.C03EnergyParallelJets

/-! A linear-in-time acceleration correction changes its covariant time
derivative by exactly the ordinary endpoint correction field. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau.LeafProofs L23Aux
set_option backward.isDefEq.respectTransparency false

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covariant_time_difference_of_germ
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (Z₁ Z₀ A₁ A₀ : ℂ × ℝ → E)
    (R : E) (t : ℝ)
    (hA₁ : DifferentiableAt ℝ A₁ (0, t)) (hA₀ : DifferentiableAt ℝ A₀ (0, t))
    (hZ : Z₁ (0, t) = Z₀ (0, t))
    (hT : mapDirection Z₁ (0, 1) (0, t) = mapDirection Z₀ (0, 1) (0, t))
    (hA : (fun s => A₁ (0, s)) =ᶠ[𝓝 t] (fun s => A₀ (0, s) + s • R)) :
    mapCovariantD Γ Z₁ (0, 1) A₁ (0, t) -
      mapCovariantD Γ Z₀ (0, 1) A₀ (0, t) =
      R + Γ (Z₀ (0, t)) (mapDirection Z₀ (0, 1) (0, t)) (t • R) := by
  have hd₀ : DifferentiableAt ℝ (fun s : ℝ => A₀ (0, s)) t :=
    hA₀.comp t (((hasDerivAt_const t (0 : ℂ)).prodMk (hasDerivAt_id t)).differentiableAt)
  have hd := hd₀.hasDerivAt.add ((hasDerivAt_id t).smul_const R)
  have hdval : deriv (fun s => A₀ (0, s) + s • R) t =
      deriv (fun s => A₀ (0, s)) t + R := by
    convert! hd.deriv using 1 <;> simp only [Pi.add_apply, id_eq, one_smul]
  have hv : A₁ (0, t) = A₀ (0, t) + t • R := hA.self_of_nhds
  unfold mapCovariantD
  rw [mapDirection_time A₁ hA₁, mapDirection_time A₀ hA₀, hA.deriv_eq, hdval, hZ, hT, hv]
  simp only [one_smul, map_add]
  abel

end Yau.Proofs.C03Aux
