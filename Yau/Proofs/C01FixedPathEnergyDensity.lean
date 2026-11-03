import Yau.Proofs.C01FamilyPathEnergyDensity

/-! A fixed actual path has a jointly C2 energy density in metric
time and path parameter. Its genuine time derivative is minus the
actual real Ricci quadratic of that path velocity. -/

noncomputable section
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint Yau.LeafProofs.L12Aux

variable {n : ℕ} {M : ComplexManifold n}

def fixedActualPathEnergyDensity (h : ℝ → HermitianField M) (f : ℝ → M.Carrier) (p : ℝ × ℝ) : ℝ :=
  actualPathSpeed (h p.1) f p.2 ^ 2

theorem fixedActualPathEnergyDensity_contDiffOn_two
    (h : ℝ → HermitianField M) (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J)
    (hh : MetricFamilySmooth h I) (f : ℝ → M.Carrier) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 f J →
    ContDiffOn ℝ 2 (fixedActualPathEnergyDensity h f) (I ×ˢ J) := by
  letI := manifold_realSmooth M
  intro hf
  let F : ℝ → ℝ → M.Carrier := fun _ u => f u
  have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) 3
      (Prod.snd : ℝ × ℝ → ℝ) ((Set.univ : Set ℝ) ×ˢ J) :=
    (contDiffOn_snd : ContDiffOn ℝ 3 (Prod.snd : ℝ × ℝ → ℝ) _).contMDiffOn
  have hF : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry F) ((Set.univ : Set ℝ) ×ˢ J) :=
    hf.comp hsnd (fun p hp => hp.2)
  have HD := familyActualPathEnergyDensity_contDiffOn_two h I hI hh F Set.univ J isOpen_univ hJ hF
  have hγ : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (((0 : ℝ), p.1), p.2)) (I ×ˢ J) :=
    (contDiffOn_const.prodMk contDiffOn_fst).prodMk contDiffOn_snd
  have HC := HD.comp hγ (fun p hp => ⟨⟨Set.mem_univ _, hp.1⟩, hp.2⟩)
  exact HC

variable {X : KahlerManifold n} {o : Pt X} {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_fixed_energyDensity_hasDerivAt
    (hflow : LocalizedFlow X o h U P ρ) (f : ℝ → Pt X) (u a : ℝ) (ha : 0 < a) :
    HasDerivAt (fun t => fixedActualPathEnergyDensity h f (t, u))
      (-actualRealRicciQuadratic (h a) (f u) (realCurveVelocity f u)) a := by
  have hfun : (fun t => fixedActualPathEnergyDensity h f (t, u)) =
      (fun t => realTangentSpeedSq (h t) (f u) (realCurveVelocity f u)) := by
    funext t
    exact actualPathSpeed_sq (h t) f u
  rw [hfun]
  exact localizedFlow_realTangentSpeedSq_hasDerivAt hflow (f u) (realCurveVelocity f u) a ha

end Yau.NodeProofs.C01Aux
