import GroupExtension.Defs
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

namespace GroupExtension

variable {N E G : Type} [CommGroup N] [Group E] [Group G] (S : GroupExtension N E G)

namespace Splitting

#check Rep.ofMulDistribMulAction -- requires G and N to be a term of `Type`, not `Type*`
noncomputable def toRep (φ : G →* MulAut N) : Rep ℤ G := @Rep.ofMulDistribMulAction G N _ _ (MulDistribMulAction.compHom N φ)
-- #check (Splitting S) ≃ groupCohomology.H1 (toRep ) -- requires showing that `Splitting.conjAct : G →* MulAut N` is unique regardless of the choice of `Splitting.sectionHom : G →* E`

end Splitting

#check Rep.ofMulDistribMulAction
#check groupCohomology.H2

end GroupExtension
