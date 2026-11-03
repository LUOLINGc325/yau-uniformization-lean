import Yau.Proofs.C04MetricDecay
import Yau.Proofs.C04IntrinsicWindows
import Yau.Proofs.C04BoundedGeometryCharts

/-! The literal original Ricci-window contract, conditional only on its three
registered predecessor contracts. All charts use the same selected clock tail. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint BlueprintContracts

theorem C04_of_originalC01_C02_C03
    (hC01 : C01_contract) (hC02 : C02_contract) (hC03 : C03_contract) : C04_contract := by
  intro n X o h U P ρ hf
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ :=
    first_seven_of_originalC01_C02_C03 hC01 hC02 hC03 n X o h U P ρ hf
  obtain ⟨a, b, ha, ha1, hb, hmin, S, K, hSinf, hwindow, tw, htwpos, htwinf,
    hmiddle, hratio, θ, hθ, lambda0, hlambda0, hRpos, hcenter, htube⟩ :=
    intrinsic_windows_of_originalC01_C02_C03 hC01 hC02 hC03 n X o h U P ρ hf
  dsimp only [RicciWindows]
  refine ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, a, b, ha, ha1, hb, hmin, S, K, hSinf,
    hwindow, tw, htwpos, htwinf, hmiddle, hratio, θ, hθ, lambda0, hlambda0,
    hRpos, hcenter, ?_⟩
  intro r hr
  obtain ⟨bcurv, hbcurv, Kjet, hKjet, hjets⟩ := htube r hr
  obtain ⟨rc, c, C, hrc, hc, hC, Cm, hCm, hcharts⟩ :=
    C04ChartsAux.quantitativeHolomorphicCharts_all_dimensions n bcurv hbcurv Kjet hKjet
  refine ⟨rc, c, C, hrc, hc, Cm, ?_⟩
  intro i hRi
  intro p hp z hz htime
  obtain ⟨htimepos, hsmooth, hkahler, hcomplete, hcurv⟩ := hjets i hRi p hp z hz
  exact hcharts X.manifold _ p hsmooth hkahler hcomplete hcurv

end Yau.Proofs.C04Aux
