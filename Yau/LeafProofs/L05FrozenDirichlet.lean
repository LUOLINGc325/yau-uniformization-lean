import Yau.LeafProofs.L05PerronConstruction

noncomputable section

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem frozenBellmanDirichletGap_proved : FrozenBellmanDirichletGap := by
  intro n hn ell L hell hL F hF hE hconc h0 g B hB hg hgb
  obtain ⟨hG,hGeq,hGb⟩ := perron_data_extension hg hgb
  obtain ⟨v,hvc,hve,hvs,hvb⟩ := perron_construct hn hell hL hF hE h0 hB
    hG.continuous.continuousOn (fun q _ => hGb q)
  refine ⟨v,hvc.mono unitClosed_subset_perronSlab,?_,?_,?_⟩
  · intro p hp
    exact (hve (parabolicBoundary_subset_perronBoundary hp)).trans
      (hGeq (perron_truncatedBoundary_closed (by norm_num : (-1:ℝ) ≤ 0) hp))
  · exact ⟨viscositySub_mono_domain hvs.1 unitOpen_subset_perronOpen,
      viscositySuper_mono_domain hvs.2 unitOpen_subset_perronOpen⟩
  · intro p hp
    exact hvb p (unitClosed_subset_perronSlab hp)

end Yau.LeafProofs.L05Aux
